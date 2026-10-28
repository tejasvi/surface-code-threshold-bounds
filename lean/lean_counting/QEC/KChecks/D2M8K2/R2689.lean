import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10756 = true := by
  decide +kernel

theorem tot10756 : totK PD2M8K2 D2M8K2.t10756 = [0, 0, 0, 206439909265, 489923674840, 168745971540, 5253830308, 0] := by
  decide +kernel

theorem rows10757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10757 = true := by
  decide +kernel

theorem tot10757 : totK PD2M8K2 D2M8K2.t10757 = [0, 0, 0, 170791154550, 474369288266, 197125475088, 10615343189, 0] := by
  decide +kernel

theorem rows10758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10758 = true := by
  decide +kernel

theorem tot10758 : totK PD2M8K2 D2M8K2.t10758 = [0, 0, 0, 62434004099, 347786962579, 337488833681, 55005540901, 1138244013] := by
  decide +kernel

theorem rows10759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10759 = true := by
  decide +kernel

theorem tot10759 : totK PD2M8K2 D2M8K2.t10759 = [0, 0, 0, 91054546602, 424913093788, 327465920107, 30266216104, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
