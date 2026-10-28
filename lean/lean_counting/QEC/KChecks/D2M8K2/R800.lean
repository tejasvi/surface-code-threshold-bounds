import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3200 = true := by
  decide +kernel

theorem tot3200 : totK PD2M8K2 D2M8K2.t3200 = [0, 173847997180, 461016296104, 249619618277, 20848005397, 0, 0, 0] := by
  decide +kernel

theorem rows3201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3201 = true := by
  decide +kernel

theorem tot3201 : totK PD2M8K2 D2M8K2.t3201 = [0, 181529627328, 472783876718, 243058864770, 13501431596, 0, 0, 0] := by
  decide +kernel

theorem rows3202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3202 = true := by
  decide +kernel

theorem tot3202 : totK PD2M8K2 D2M8K2.t3202 = [162052656816, 390403641584, 224431219288, 87358482077, 12293754876, 0, 0, 0] := by
  decide +kernel

theorem rows3203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3203 = true := by
  decide +kernel

theorem tot3203 : totK PD2M8K2 D2M8K2.t3203 = [193218292144, 471234535758, 217384368965, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
