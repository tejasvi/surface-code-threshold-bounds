import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1152 = true := by
  decide +kernel

theorem tot1152 : totK PA10K2 A10K2.t1152 = [0, 0, 444487269486, 1796180985446, 1998683336950, 571705952670, 34548791282, 0, 0, 0] := by
  decide +kernel

theorem rows1153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1153 = true := by
  decide +kernel

theorem tot1153 : totK PA10K2 A10K2.t1153 = [0, 0, 0, 553055028005, 1954264499299, 1671117027623, 395834075734, 25239774317, 0, 0] := by
  decide +kernel

theorem rows1154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1154 = true := by
  decide +kernel

theorem tot1154 : totK PA10K2 A10K2.t1154 = [0, 0, 347741869782, 1480562786334, 1925639463343, 891573749297, 150685979414, 5410721913, 0, 0] := by
  decide +kernel

theorem rows1155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1155 = true := by
  decide +kernel

theorem tot1155 : totK PA10K2 A10K2.t1155 = [0, 0, 372058034639, 1623159742971, 1958009882341, 557177824681, 32744407728, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
