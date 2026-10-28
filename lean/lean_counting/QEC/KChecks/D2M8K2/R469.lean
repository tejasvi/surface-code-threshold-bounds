import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1876 = true := by
  decide +kernel

theorem tot1876 : totK PD2M8K2 D2M8K2.t1876 = [0, 0, 269475195316, 500887528956, 115880932082, 1369150432, 0, 0] := by
  decide +kernel

theorem rows1877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1877 = true := by
  decide +kernel

theorem tot1877 : totK PD2M8K2 D2M8K2.t1877 = [0, 90904776651, 385276044431, 389740444073, 47187848622, 0, 0, 0] := by
  decide +kernel

theorem rows1878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1878 = true := by
  decide +kernel

theorem tot1878 : totK PD2M8K2 D2M8K2.t1878 = [0, 204271871632, 453901456445, 224295273277, 20086524430, 0, 0, 0] := by
  decide +kernel

theorem rows1879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1879 = true := by
  decide +kernel

theorem tot1879 : totK PD2M8K2 D2M8K2.t1879 = [0, 91010644896, 390430698042, 343919904838, 72565868817, 10210320223, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
