import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t936 = true := by
  decide +kernel

theorem tot936 : totK PD2M8K2 D2M8K2.t936 = [0, 213164104720, 481276347308, 187000451834, 9661765460, 0, 0, 0] := by
  decide +kernel

theorem rows937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t937 = true := by
  decide +kernel

theorem tot937 : totK PD2M8K2 D2M8K2.t937 = [90425197987, 330628465091, 364251711923, 99925566622, 3575904516, 0, 0, 0] := by
  decide +kernel

theorem rows938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t938 = true := by
  decide +kernel

theorem tot938 : totK PD2M8K2 D2M8K2.t938 = [168906687206, 434583702633, 277858936606, 30376448897, 0, 0, 0, 0] := by
  decide +kernel

theorem rows939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t939 = true := by
  decide +kernel

theorem tot939 : totK PD2M8K2 D2M8K2.t939 = [164578067488, 474073359906, 251434052070, 13887397069, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
