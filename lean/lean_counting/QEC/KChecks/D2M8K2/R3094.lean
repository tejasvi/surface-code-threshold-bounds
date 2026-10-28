import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12376 = true := by
  decide +kernel

theorem tot12376 : totK PD2M8K2 D2M8K2.t12376 = [0, 196281402722, 491412220441, 226211141114, 10140659148, 0, 0, 0] := by
  decide +kernel

theorem rows12377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12377 = true := by
  decide +kernel

theorem tot12377 : totK PD2M8K2 D2M8K2.t12377 = [0, 54786548592, 277805650423, 380924212538, 175405831364, 21400436502, 0, 0] := by
  decide +kernel

theorem rows12378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12378 = true := by
  decide +kernel

theorem tot12378 : totK PD2M8K2 D2M8K2.t12378 = [0, 0, 208508424819, 483253912549, 204474144668, 7994456143, 0, 0] := by
  decide +kernel

theorem rows12379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12379 = true := by
  decide +kernel

theorem tot12379 : totK PD2M8K2 D2M8K2.t12379 = [0, 66560335648, 240658197804, 392141191346, 181844122905, 8104085798, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
