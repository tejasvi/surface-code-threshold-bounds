import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12412 = true := by
  decide +kernel

theorem tot12412 : totK PD2M8K2 D2M8K2.t12412 = [0, 72850490491, 344463909909, 390427226749, 74149901028, 1181638453, 0, 0] := by
  decide +kernel

theorem rows12413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12413 = true := by
  decide +kernel

theorem tot12413 : totK PD2M8K2 D2M8K2.t12413 = [0, 42288979907, 279337086434, 448549691073, 122885790503, 3699256714, 0, 0] := by
  decide +kernel

theorem rows12414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12414 = true := by
  decide +kernel

theorem tot12414 : totK PD2M8K2 D2M8K2.t12414 = [0, 201573480756, 482442008248, 192560785061, 9781969705, 0, 0, 0] := by
  decide +kernel

theorem rows12415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12415 = true := by
  decide +kernel

theorem tot12415 : totK PD2M8K2 D2M8K2.t12415 = [0, 161519316633, 458014183746, 250100898707, 13795945806, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
