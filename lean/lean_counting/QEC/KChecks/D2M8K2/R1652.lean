import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6608 = true := by
  decide +kernel

theorem tot6608 : totK PD2M8K2 D2M8K2.t6608 = [0, 0, 327629517376, 452828578251, 81453632088, 1095107716, 0, 0] := by
  decide +kernel

theorem rows6609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6609 = true := by
  decide +kernel

theorem tot6609 : totK PD2M8K2 D2M8K2.t6609 = [0, 73602475273, 313597493237, 384048652588, 108623961797, 3882006667, 0, 0] := by
  decide +kernel

theorem rows6610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6610 = true := by
  decide +kernel

theorem tot6610 : totK PD2M8K2 D2M8K2.t6610 = [0, 189447218422, 480040588176, 211935252706, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows6611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6611 = true := by
  decide +kernel

theorem tot6611 : totK PD2M8K2 D2M8K2.t6611 = [0, 169319566974, 460896317820, 243430779491, 13795945806, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
