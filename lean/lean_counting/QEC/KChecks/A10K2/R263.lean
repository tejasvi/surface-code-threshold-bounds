import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1052 = true := by
  decide +kernel

theorem tot1052 : totK PA10K2 A10K2.t1052 = [0, 0, 516133124082, 1860816201788, 1909839328370, 530689745646, 31908368213, 0, 0, 0] := by
  decide +kernel

theorem rows1053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1053 = true := by
  decide +kernel

theorem tot1053 : totK PA10K2 A10K2.t1053 = [0, 0, 227459092167, 1246878446820, 2166140349951, 1259194053497, 154793644322, 0, 0, 0] := by
  decide +kernel

theorem rows1054 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1054 = true := by
  decide +kernel

theorem tot1054 : totK PA10K2 A10K2.t1054 = [0, 0, 223045939950, 963727484315, 1836743478217, 1511581329198, 325716154996, 12692412833, 0, 0] := by
  decide +kernel

theorem rows1055 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1055 = true := by
  decide +kernel

theorem tot1055 : totK PA10K2 A10K2.t1055 = [0, 0, 455931948416, 1818074767176, 2072565809257, 608604939677, 29194255750, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
