import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4264 = true := by
  decide +kernel

theorem tot4264 : totK PD2M8K2 D2M8K2.t4264 = [0, 0, 0, 45367520076, 237021152907, 419753948606, 137674088153, 5320761635] := by
  decide +kernel

theorem rows4265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4265 = true := by
  decide +kernel

theorem tot4265 : totK PD2M8K2 D2M8K2.t4265 = [0, 0, 0, 203430951961, 496289605196, 195842667125, 9775555886, 0] := by
  decide +kernel

theorem rows4266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4266 = true := by
  decide +kernel

theorem tot4266 : totK PD2M8K2 D2M8K2.t4266 = [0, 0, 0, 157841096676, 475061404967, 239997147766, 10706759353, 0] := by
  decide +kernel

theorem rows4267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4267 = true := by
  decide +kernel

theorem tot4267 : totK PD2M8K2 D2M8K2.t4267 = [0, 0, 0, 0, 374161491170, 446327054656, 42205140645, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
