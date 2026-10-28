import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6240 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6240 = true := by
  decide +kernel

theorem tot6240 : totK PA10K2 A10K2.t6240 = [0, 0, 518259217515, 1797800393556, 1826415534834, 563869444631, 48666249715, 0, 0, 0] := by
  decide +kernel

theorem rows6241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6241 = true := by
  decide +kernel

theorem tot6241 : totK PA10K2 A10K2.t6241 = [0, 0, 501084729324, 1886594134477, 2029780722076, 545299200399, 32766700772, 0, 0, 0] := by
  decide +kernel

theorem rows6242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6242 = true := by
  decide +kernel

theorem tot6242 : totK PA10K2 A10K2.t6242 = [0, 288429583321, 958507800701, 1570144837496, 1595531065678, 600989249639, 50548650670, 0, 0, 0] := by
  decide +kernel

theorem rows6243 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6243 = true := by
  decide +kernel

theorem tot6243 : totK PA10K2 A10K2.t6243 = [0, 491397727675, 1915791292466, 2049202686527, 545362138369, 32256115688, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
