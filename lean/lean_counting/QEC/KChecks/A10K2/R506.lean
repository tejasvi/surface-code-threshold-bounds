import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2024 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2024 = true := by
  decide +kernel

theorem tot2024 : totK PA10K2 A10K2.t2024 = [0, 0, 0, 290308046095, 1303349884099, 1971264659854, 1080768292344, 178035568580, 6318667960, 0] := by
  decide +kernel

theorem rows2025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2025 = true := by
  decide +kernel

theorem tot2025 : totK PA10K2 A10K2.t2025 = [0, 0, 0, 435413342471, 1763709872942, 2096756797933, 636021706056, 24993131327, 0, 0] := by
  decide +kernel

theorem rows2026 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2026 = true := by
  decide +kernel

theorem tot2026 : totK PA10K2 A10K2.t2026 = [0, 0, 0, 81159475686, 834053039520, 2072516005229, 1607481265645, 264384260029, 6439430839, 0] := by
  decide +kernel

theorem rows2027 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2027 = true := by
  decide +kernel

theorem tot2027 : totK PA10K2 A10K2.t2027 = [0, 0, 0, 463855939988, 1864268000495, 1989983215004, 526532830428, 22108643497, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
