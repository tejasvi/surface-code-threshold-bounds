import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14652 = true := by
  decide +kernel

theorem tot14652 : totK PD2M8K2 D2M8K2.t14652 = [0, 200817510337, 474737000699, 220954241203, 12784758018, 0, 0, 0] := by
  decide +kernel

theorem rows14653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14653 = true := by
  decide +kernel

theorem tot14653 : totK PD2M8K2 D2M8K2.t14653 = [0, 125019189415, 433191433410, 310681639670, 35705055619, 0, 0, 0] := by
  decide +kernel

theorem rows14654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14654 = true := by
  decide +kernel

theorem tot14654 : totK PD2M8K2 D2M8K2.t14654 = [0, 0, 183476156577, 462554122234, 229078373580, 19572653258, 0, 0] := by
  decide +kernel

theorem rows14655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14655 = true := by
  decide +kernel

theorem tot14655 : totK PD2M8K2 D2M8K2.t14655 = [0, 0, 171917482928, 486748153943, 214580641336, 5430665091, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
