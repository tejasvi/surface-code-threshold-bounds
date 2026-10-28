import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6200 = true := by
  decide +kernel

theorem tot6200 : totK PD2M8K2 D2M8K2.t6200 = [123250812643, 433185526583, 314867510811, 36312412705, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6201 = true := by
  decide +kernel

theorem tot6201 : totK PD2M8K2 D2M8K2.t6201 = [0, 173650599941, 450912984835, 260428614941, 25354272529, 0, 0, 0] := by
  decide +kernel

theorem rows6202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6202 = true := by
  decide +kernel

theorem tot6202 : totK PD2M8K2 D2M8K2.t6202 = [0, 184883224589, 495444157671, 210989283033, 5216525738, 0, 0, 0] := by
  decide +kernel

theorem rows6203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6203 = true := by
  decide +kernel

theorem tot6203 : totK PD2M8K2 D2M8K2.t6203 = [176559373540, 427211200009, 232662046066, 71826065049, 6777409681, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
