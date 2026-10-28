import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t980 = true := by
  decide +kernel

theorem tot980 : totK PA10K2 A10K2.t980 = [0, 0, 292098887399, 1425981622536, 2147556788844, 935333363269, 72946620043, 0, 0, 0] := by
  decide +kernel

theorem rows981 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t981 = true := by
  decide +kernel

theorem tot981 : totK PA10K2 A10K2.t981 = [0, 0, 0, 505271909268, 1845221431503, 1796921955384, 481003784682, 30831673886, 0, 0] := by
  decide +kernel

theorem rows982 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t982 = true := by
  decide +kernel

theorem tot982 : totK PA10K2 A10K2.t982 = [0, 0, 479736365516, 1656428943102, 1891473842057, 742065423715, 66162645450, 0, 0, 0] := by
  decide +kernel

theorem rows983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t983 = true := by
  decide +kernel

theorem tot983 : totK PA10K2 A10K2.t983 = [0, 0, 162060387465, 1303882205099, 2239618115350, 877775634996, 65428238762, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
