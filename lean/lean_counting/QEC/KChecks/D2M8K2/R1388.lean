import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5552 = true := by
  decide +kernel

theorem tot5552 : totK PD2M8K2 D2M8K2.t5552 = [54772459227, 343513001832, 410139800232, 79035412395, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows5553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5553 = true := by
  decide +kernel

theorem tot5553 : totK PD2M8K2 D2M8K2.t5553 = [18464490943, 273355754768, 474731783567, 125236506660, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows5554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5554 = true := by
  decide +kernel

theorem tot5554 : totK PD2M8K2 D2M8K2.t5554 = [188360419149, 460404211668, 244385926736, 21577357534, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5555 = true := by
  decide +kernel

theorem tot5555 : totK PD2M8K2 D2M8K2.t5555 = [204609578098, 470107973459, 218104468370, 14226557864, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
