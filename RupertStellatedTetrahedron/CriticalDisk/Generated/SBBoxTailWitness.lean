import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxTailChunk0
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxTailChunk1
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxTailChunk2
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxTailChunk3
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxTailChunk4
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxTailChunk5
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxTailChunk6
import RupertStellatedTetrahedron.CriticalDisk.Generated.SBBoxTailChunk7

/-! Aggregated generated exact `(SB-box)` tail replay manifest. -/

noncomputable section

namespace RupertStellatedTetrahedron

namespace GeneratedSBBoxTailWitness

def sourceSHA256 : String := "28c78e00a4c7f192f7a5ff0e9edecbaa856c6c7b9996357fcbd874f109410f54"
def omittedFailRows : Nat := 40

def rows : List SBBoxTailRow :=
    SBBoxTailChunk0.rows ++
    SBBoxTailChunk1.rows ++
    SBBoxTailChunk2.rows ++
    SBBoxTailChunk3.rows ++
    SBBoxTailChunk4.rows ++
    SBBoxTailChunk5.rows ++
    SBBoxTailChunk6.rows ++
    SBBoxTailChunk7.rows

def manifest : SBBoxTailManifest where
  rows := rows
  inputHash := "sbd3_witness.jsonl"
  outputHash := sourceSHA256

theorem rows_length : rows.length = 2797 := by
  native_decide

theorem omittedFailRows_eq : omittedFailRows = 40 := by
  native_decide

theorem rows_valid_mem :
    ∀ row ∈ rows, row.validBool = true := by
  intro row h
  simp [rows] at h
  rcases h with h | h | h | h | h | h | h | h
  · exact SBBoxTailChunk0.rows_valid_mem row h
  · exact SBBoxTailChunk1.rows_valid_mem row h
  · exact SBBoxTailChunk2.rows_valid_mem row h
  · exact SBBoxTailChunk3.rows_valid_mem row h
  · exact SBBoxTailChunk4.rows_valid_mem row h
  · exact SBBoxTailChunk5.rows_valid_mem row h
  · exact SBBoxTailChunk6.rows_valid_mem row h
  · exact SBBoxTailChunk7.rows_valid_mem row h

theorem manifest_rowsValid : manifest.RowsValid where
  rows_valid := by
    simpa [manifest] using rows_valid_mem

end GeneratedSBBoxTailWitness

end RupertStellatedTetrahedron
