import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7892 = true := by
  decide +kernel

theorem tot7892 : totK PA10K2 A10K2.t7892 = [0, 0, 165720869238, 965438774924, 2058526654152, 1537112625714, 277305926461, 7007974415, 0, 0] := by
  decide +kernel

theorem rows7893 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7893 = true := by
  decide +kernel

theorem tot7893 : totK PA10K2 A10K2.t7893 = [0, 0, 511648895979, 1883335735980, 1933657606278, 527787743656, 31908368213, 0, 0, 0] := by
  decide +kernel

theorem rows7894 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7894 = true := by
  decide +kernel

theorem tot7894 : totK PA10K2 A10K2.t7894 = [0, 0, 118398086739, 946647337662, 2082237400095, 1487933345748, 315475192075, 18710738642, 0, 0] := by
  decide +kernel

theorem rows7895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7895 = true := by
  decide +kernel

theorem tot7895 : totK PA10K2 A10K2.t7895 = [0, 0, 253046812372, 1122667021754, 1944420087015, 1371426014962, 245738274739, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
