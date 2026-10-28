import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9648 = true := by
  decide +kernel

theorem tot9648 : totK PD2M8K2 D2M8K2.t9648 = [0, 0, 212112106910, 495476675344, 190132827370, 5364914253, 0, 0] := by
  decide +kernel

theorem rows9649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9649 = true := by
  decide +kernel

theorem tot9649 : totK PD2M8K2 D2M8K2.t9649 = [0, 142385201976, 351380718472, 299182910253, 116345587210, 6804944647, 0, 0] := by
  decide +kernel

theorem rows9650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9650 = true := by
  decide +kernel

theorem tot9650 : totK PD2M8K2 D2M8K2.t9650 = [0, 171427062993, 458372232031, 246536304961, 16944580709, 0, 0, 0] := by
  decide +kernel

theorem rows9651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9651 = true := by
  decide +kernel

theorem tot9651 : totK PD2M8K2 D2M8K2.t9651 = [0, 67464307213, 347031881424, 411217268955, 84173769544, 1129489618, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
