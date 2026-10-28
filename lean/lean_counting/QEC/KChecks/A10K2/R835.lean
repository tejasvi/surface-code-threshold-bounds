import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3340 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3340 = true := by
  decide +kernel

theorem tot3340 : totK PA10K2 A10K2.t3340 = [0, 518770102172, 1965286858286, 2069716399381, 514855879058, 20174488578, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3341 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3341 = true := by
  decide +kernel

theorem tot3341 : totK PA10K2 A10K2.t3341 = [0, 0, 712636488221, 2207522651387, 1734261787309, 327226018148, 13360781053, 0, 0, 0] := by
  decide +kernel

theorem rows3342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3342 = true := by
  decide +kernel

theorem tot3342 : totK PA10K2 A10K2.t3342 = [0, 477476970137, 1767132287000, 1947233596242, 670814944121, 65350474825, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3343 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3343 = true := by
  decide +kernel

theorem tot3343 : totK PA10K2 A10K2.t3343 = [0, 307697978958, 1435749814307, 2179100818394, 1033366430715, 84654811513, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
