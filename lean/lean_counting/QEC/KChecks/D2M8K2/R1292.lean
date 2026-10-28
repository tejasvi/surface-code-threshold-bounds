import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5168 = true := by
  decide +kernel

theorem tot5168 : totK PD2M8K2 D2M8K2.t5168 = [0, 0, 0, 244187394327, 508081033983, 137689904843, 2329117419, 0] := by
  decide +kernel

theorem rows5169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5169 = true := by
  decide +kernel

theorem tot5169 : totK PD2M8K2 D2M8K2.t5169 = [0, 0, 58758900076, 250211181175, 405126608939, 156196115553, 10841558499, 0] := by
  decide +kernel

theorem rows5170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5170 = true := by
  decide +kernel

theorem tot5170 : totK PD2M8K2 D2M8K2.t5170 = [0, 0, 181847706126, 451465707935, 242382286653, 22758451065, 0, 0] := by
  decide +kernel

theorem rows5171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5171 = true := by
  decide +kernel

theorem tot5171 : totK PD2M8K2 D2M8K2.t5171 = [0, 0, 180619357860, 462563515494, 238264436171, 18069168733, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
