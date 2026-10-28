import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9660 = true := by
  decide +kernel

theorem tot9660 : totK PD2M8K2 D2M8K2.t9660 = [0, 177330415504, 425302114470, 260163327952, 52862073259, 1429815836, 0, 0] := by
  decide +kernel

theorem rows9661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9661 = true := by
  decide +kernel

theorem tot9661 : totK PD2M8K2 D2M8K2.t9661 = [0, 186216148946, 461961340520, 230677524356, 15518918465, 0, 0, 0] := by
  decide +kernel

theorem rows9662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9662 = true := by
  decide +kernel

theorem tot9662 : totK PD2M8K2 D2M8K2.t9662 = [0, 63803697449, 335650516327, 411004744441, 94252130205, 1248762627, 0, 0] := by
  decide +kernel

theorem rows9663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9663 = true := by
  decide +kernel

theorem tot9663 : totK PD2M8K2 D2M8K2.t9663 = [0, 0, 205291827447, 477084123384, 181055888277, 7352468738, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
