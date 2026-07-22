import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxBulkChunk0
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxBulkChunk1
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxBulkChunk2
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxBulkChunk3
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxBulkChunk4
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxBulkChunk5
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxBulkChunk6
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxBulkChunk7

/-! Aggregated generated `(SB-box)` bulk/seam replay manifest. -/

noncomputable section

namespace RupertStellatedTetrahedron

namespace GeneratedSBBoxBulkWitness

def sourceSHA256 : String := "1ee114f1a60d036fd489b9a4271897cf5eecf76af86401f1c09309a12a2994e1"
def etaBudget : ℚ := 1 / 500

def rows : List SBBoxBulkRow :=
    SBBoxBulkChunk0.rows ++
    SBBoxBulkChunk1.rows ++
    SBBoxBulkChunk2.rows ++
    SBBoxBulkChunk3.rows ++
    SBBoxBulkChunk4.rows ++
    SBBoxBulkChunk5.rows ++
    SBBoxBulkChunk6.rows ++
    SBBoxBulkChunk7.rows

def manifest : SBBoxBulkManifest where
  rows := rows
  inputHash := "manifest_sbbox_bulk_*.json"
  outputHash := sourceSHA256

theorem rows_length : rows.length = 1690 := by
  native_decide

theorem rows_valid_mem :
    ∀ row ∈ rows, row.validBool etaBudget = true := by
  intro row h
  simp [rows] at h
  rcases h with h | h | h | h | h | h | h | h
  · exact SBBoxBulkChunk0.rows_valid_mem row h
  · exact SBBoxBulkChunk1.rows_valid_mem row h
  · exact SBBoxBulkChunk2.rows_valid_mem row h
  · exact SBBoxBulkChunk3.rows_valid_mem row h
  · exact SBBoxBulkChunk4.rows_valid_mem row h
  · exact SBBoxBulkChunk5.rows_valid_mem row h
  · exact SBBoxBulkChunk6.rows_valid_mem row h
  · exact SBBoxBulkChunk7.rows_valid_mem row h

theorem manifest_rowsValid :
    manifest.RowsValid etaBudget where
  rows_valid := by
    simpa [manifest] using rows_valid_mem

end GeneratedSBBoxBulkWitness

end RupertStellatedTetrahedron
