import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11232 = true := by
  decide +kernel

theorem tot11232 : totK PD2M8K2 D2M8K2.t11232 = [75805549015, 365636199223, 403405759723, 71548852488, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11233 = true := by
  decide +kernel

theorem tot11233 : totK PD2M8K2 D2M8K2.t11233 = [0, 201765773257, 474431154559, 178846075434, 7205897528, 0, 0, 0] := by
  decide +kernel

theorem rows11234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11234 = true := by
  decide +kernel

theorem tot11234 : totK PD2M8K2 D2M8K2.t11234 = [0, 150599342317, 440268433493, 293662182727, 31996124229, 0, 0, 0] := by
  decide +kernel

theorem rows11235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11235 = true := by
  decide +kernel

theorem tot11235 : totK PD2M8K2 D2M8K2.t11235 = [0, 190534893553, 469521748926, 237054166480, 16217039482, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
