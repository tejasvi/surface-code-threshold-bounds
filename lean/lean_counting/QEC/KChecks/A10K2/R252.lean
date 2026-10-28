import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1008 = true := by
  decide +kernel

theorem tot1008 : totK PA10K2 A10K2.t1008 = [0, 293192342777, 1171247568493, 1870016080952, 1283706504254, 229019348969, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows1009 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1009 = true := by
  decide +kernel

theorem tot1009 : totK PA10K2 A10K2.t1009 = [0, 269012435216, 1519531621254, 2176369091140, 788041829763, 53838005252, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1010 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1010 = true := by
  decide +kernel

theorem tot1010 : totK PA10K2 A10K2.t1010 = [0, 236218266661, 1140182995672, 2079109925015, 1238059712263, 181440386798, 5982052406, 0, 0, 0] := by
  decide +kernel

theorem rows1011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1011 = true := by
  decide +kernel

theorem tot1011 : totK PA10K2 A10K2.t1011 = [0, 550983302686, 1946334108174, 1933235561620, 535098441541, 32801252013, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
