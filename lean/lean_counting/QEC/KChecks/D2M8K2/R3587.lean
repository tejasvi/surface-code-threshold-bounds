import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14348 = true := by
  decide +kernel

theorem tot14348 : totK PD2M8K2 D2M8K2.t14348 = [0, 172333883661, 461173864010, 249075824708, 16742150748, 0, 0, 0] := by
  decide +kernel

theorem rows14349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14349 = true := by
  decide +kernel

theorem tot14349 : totK PD2M8K2 D2M8K2.t14349 = [0, 0, 189197306086, 463376295190, 239932196539, 18567029682, 0, 0] := by
  decide +kernel

theorem rows14350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14350 = true := by
  decide +kernel

theorem tot14350 : totK PD2M8K2 D2M8K2.t14350 = [0, 0, 220424266797, 502899317499, 163109459016, 2560221221, 0, 0] := by
  decide +kernel

theorem rows14351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14351 = true := by
  decide +kernel

theorem tot14351 : totK PD2M8K2 D2M8K2.t14351 = [0, 176264834056, 447647933536, 248411534923, 47508730072, 2961673374, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
