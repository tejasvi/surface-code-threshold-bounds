import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5800 = true := by
  decide +kernel

theorem tot5800 : totK PD2M8K2 D2M8K2.t5800 = [0, 189968442768, 488310040252, 228228878946, 10362833894, 0, 0, 0] := by
  decide +kernel

theorem rows5801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5801 = true := by
  decide +kernel

theorem tot5801 : totK PD2M8K2 D2M8K2.t5801 = [0, 70959913557, 301883501056, 376020236897, 156585591582, 17176948997, 0, 0] := by
  decide +kernel

theorem rows5802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5802 = true := by
  decide +kernel

theorem tot5802 : totK PD2M8K2 D2M8K2.t5802 = [0, 0, 206274217393, 468057038844, 203025503107, 11867500000, 0, 0] := by
  decide +kernel

theorem rows5803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5803 = true := by
  decide +kernel

theorem tot5803 : totK PD2M8K2 D2M8K2.t5803 = [0, 66905027861, 232142295613, 399248812674, 178442256645, 7877424857, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
