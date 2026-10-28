import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5992 = true := by
  decide +kernel

theorem tot5992 : totK PD2M8K2 D2M8K2.t5992 = [0, 0, 182388125325, 441928460215, 241337671611, 14734639880, 0, 0] := by
  decide +kernel

theorem rows5993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5993 = true := by
  decide +kernel

theorem tot5993 : totK PD2M8K2 D2M8K2.t5993 = [0, 0, 75592533057, 418770523944, 367043293535, 47205345794, 0, 0] := by
  decide +kernel

theorem rows5994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5994 = true := by
  decide +kernel

theorem tot5994 : totK PD2M8K2 D2M8K2.t5994 = [0, 0, 0, 204182711361, 505270476823, 145788621445, 2437267027, 0] := by
  decide +kernel

theorem rows5995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5995 = true := by
  decide +kernel

theorem tot5995 : totK PD2M8K2 D2M8K2.t5995 = [0, 175368045151, 413823448195, 165486278557, 63424271814, 69057510705, 6701800220, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
