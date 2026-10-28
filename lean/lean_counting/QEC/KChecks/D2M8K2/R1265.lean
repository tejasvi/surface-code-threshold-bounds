import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5060 = true := by
  decide +kernel

theorem tot5060 : totK PD2M8K2 D2M8K2.t5060 = [0, 0, 167337336085, 477248669994, 255916622277, 13726510725, 0, 0] := by
  decide +kernel

theorem rows5061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5061 = true := by
  decide +kernel

theorem tot5061 : totK PD2M8K2 D2M8K2.t5061 = [0, 0, 178799068902, 443728260748, 246739032852, 25236344470, 0, 0] := by
  decide +kernel

theorem rows5062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5062 = true := by
  decide +kernel

theorem tot5062 : totK PD2M8K2 D2M8K2.t5062 = [0, 0, 190598932983, 482577882595, 219183397157, 12439805748, 0, 0] := by
  decide +kernel

theorem rows5063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5063 = true := by
  decide +kernel

theorem tot5063 : totK PD2M8K2 D2M8K2.t5063 = [0, 0, 59293692021, 336329230019, 396389366084, 81659484933, 1171084559, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
