import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2948 = true := by
  decide +kernel

theorem tot2948 : totK PD2M8K2 D2M8K2.t2948 = [19735703396, 317515005822, 460006503618, 101967390688, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows2949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2949 = true := by
  decide +kernel

theorem tot2949 : totK PD2M8K2 D2M8K2.t2949 = [0, 207573871442, 485696410987, 185156792729, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows2950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2950 = true := by
  decide +kernel

theorem tot2950 : totK PD2M8K2 D2M8K2.t2950 = [0, 183895156851, 466133957868, 220147463470, 14707859566, 0, 0, 0] := by
  decide +kernel

theorem rows2951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2951 = true := by
  decide +kernel

theorem tot2951 : totK PD2M8K2 D2M8K2.t2951 = [0, 175867684451, 467006711820, 224745479018, 9064506700, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
