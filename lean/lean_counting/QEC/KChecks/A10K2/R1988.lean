import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7952 = true := by
  decide +kernel

theorem tot7952 : totK PA10K2 A10K2.t7952 = [0, 0, 0, 310128979065, 1522484150924, 2139156964046, 830445616400, 67721983041, 0, 0] := by
  decide +kernel

theorem rows7953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7953 = true := by
  decide +kernel

theorem tot7953 : totK PA10K2 A10K2.t7953 = [0, 0, 0, 495656028127, 1837734689644, 1942967971883, 545409596618, 28993455641, 0, 0] := by
  decide +kernel

theorem rows7954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7954 = true := by
  decide +kernel

theorem tot7954 : totK PA10K2 A10K2.t7954 = [0, 0, 0, 0, 746855768160, 2214302117927, 1498065430014, 227534232519, 7007974415, 0] := by
  decide +kernel

theorem rows7955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7955 = true := by
  decide +kernel

theorem tot7955 : totK PA10K2 A10K2.t7955 = [0, 0, 0, 669685353181, 2121185443916, 1670149695664, 219010525144, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
