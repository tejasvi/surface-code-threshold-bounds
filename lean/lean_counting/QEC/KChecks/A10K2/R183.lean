import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows732 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t732 = true := by
  decide +kernel

theorem tot732 : totK PA10K2 A10K2.t732 = [0, 514407508087, 1783185048807, 2012936928505, 710263027508, 56061662962, 0, 0, 0, 0] := by
  decide +kernel

theorem rows733 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t733 = true := by
  decide +kernel

theorem tot733 : totK PA10K2 A10K2.t733 = [0, 473843927028, 1879635225735, 1920808209560, 447768723355, 25667075836, 0, 0, 0, 0] := by
  decide +kernel

theorem rows734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t734 = true := by
  decide +kernel

theorem tot734 : totK PA10K2 A10K2.t734 = [0, 291625312176, 1421644690649, 2199214515254, 956810433849, 83200650739, 0, 0, 0, 0] := by
  decide +kernel

theorem rows735 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t735 = true := by
  decide +kernel

theorem tot735 : totK PA10K2 A10K2.t735 = [0, 0, 531632755013, 1810877654967, 1744119922329, 462133589243, 30650496230, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
