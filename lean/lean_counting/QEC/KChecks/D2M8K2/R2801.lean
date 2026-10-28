import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11204 = true := by
  decide +kernel

theorem tot11204 : totK PD2M8K2 D2M8K2.t11204 = [0, 32250561511, 279138832991, 463792369428, 120205485250, 4008488258, 0, 0] := by
  decide +kernel

theorem rows11205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11205 = true := by
  decide +kernel

theorem tot11205 : totK PD2M8K2 D2M8K2.t11205 = [0, 201647724533, 461928230953, 225559824375, 19888997542, 0, 0, 0] := by
  decide +kernel

theorem rows11206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11206 = true := by
  decide +kernel

theorem tot11206 : totK PD2M8K2 D2M8K2.t11206 = [0, 166561591980, 471616479012, 244781907479, 13657636408, 0, 0, 0] := by
  decide +kernel

theorem rows11207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11207 = true := by
  decide +kernel

theorem tot11207 : totK PD2M8K2 D2M8K2.t11207 = [0, 0, 277331492136, 504663242554, 110757816366, 1162515529, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
