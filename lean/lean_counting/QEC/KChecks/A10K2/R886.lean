import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3544 = true := by
  decide +kernel

theorem tot3544 : totK PA10K2 A10K2.t3544 = [0, 0, 201257438839, 1194267205704, 2171391637496, 1303955020469, 220602285931, 7903172220, 0, 0] := by
  decide +kernel

theorem rows3545 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3545 = true := by
  decide +kernel

theorem tot3545 : totK PA10K2 A10K2.t3545 = [0, 0, 343214772666, 1482509308185, 2112661237449, 963765717031, 93068517301, 0, 0, 0] := by
  decide +kernel

theorem rows3546 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3546 = true := by
  decide +kernel

theorem tot3546 : totK PA10K2 A10K2.t3546 = [0, 0, 437221486770, 1772924524763, 2060683183600, 724069111576, 57349480859, 0, 0, 0] := by
  decide +kernel

theorem rows3547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3547 = true := by
  decide +kernel

theorem tot3547 : totK PA10K2 A10K2.t3547 = [0, 0, 0, 589244154228, 2026716482228, 1811544980878, 412770262300, 25654631657, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
