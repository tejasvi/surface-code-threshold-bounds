import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9636 = true := by
  decide +kernel

theorem tot9636 : totK PD2M8K2 D2M8K2.t9636 = [0, 0, 140854072676, 440684480240, 272226433795, 18593226376, 0, 0] := by
  decide +kernel

theorem rows9637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9637 = true := by
  decide +kernel

theorem tot9637 : totK PD2M8K2 D2M8K2.t9637 = [0, 0, 187346021967, 477805693416, 197104600632, 6506332950, 0, 0] := by
  decide +kernel

theorem rows9638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9638 = true := by
  decide +kernel

theorem tot9638 : totK PD2M8K2 D2M8K2.t9638 = [0, 0, 191056803713, 481730057267, 210644523106, 10132347792, 0, 0] := by
  decide +kernel

theorem rows9639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9639 = true := by
  decide +kernel

theorem tot9639 : totK PD2M8K2 D2M8K2.t9639 = [0, 0, 184819700770, 488340131116, 198885387737, 6541871428, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
