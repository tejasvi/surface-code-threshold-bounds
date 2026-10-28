import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9844 = true := by
  decide +kernel

theorem tot9844 : totK PD2M8K2 D2M8K2.t9844 = [0, 0, 19895640040, 340985197068, 463792239314, 55862963458, 0, 0] := by
  decide +kernel

theorem rows9845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9845 = true := by
  decide +kernel

theorem tot9845 : totK PD2M8K2 D2M8K2.t9845 = [0, 0, 172669344232, 445476608946, 277272930036, 28146331845, 0, 0] := by
  decide +kernel

theorem rows9846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9846 = true := by
  decide +kernel

theorem tot9846 : totK PD2M8K2 D2M8K2.t9846 = [0, 0, 204366592451, 476086727632, 214995235809, 12904051658, 0, 0] := by
  decide +kernel

theorem rows9847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9847 = true := by
  decide +kernel

theorem tot9847 : totK PD2M8K2 D2M8K2.t9847 = [0, 0, 187482265692, 473460035958, 242702843570, 17565583422, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
