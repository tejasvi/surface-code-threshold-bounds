import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6896 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6896 = true := by
  decide +kernel

theorem tot6896 : totK PA10K2 A10K2.t6896 = [0, 411674496152, 1369027353806, 1425297998209, 867154479534, 575655307862, 129624216436, 5976421810, 0, 0] := by
  decide +kernel

theorem rows6897 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6897 = true := by
  decide +kernel

theorem tot6897 : totK PA10K2 A10K2.t6897 = [0, 381430224643, 1645298121901, 2067923168274, 780253588414, 66791066790, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6898 = true := by
  decide +kernel

theorem tot6898 : totK PA10K2 A10K2.t6898 = [0, 0, 557612781926, 1887159484110, 1775595291326, 474507541314, 30810868011, 0, 0, 0] := by
  decide +kernel

theorem rows6899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6899 = true := by
  decide +kernel

theorem tot6899 : totK PA10K2 A10K2.t6899 = [0, 590865579489, 1825641924944, 1877454072348, 701788093476, 58354265430, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
