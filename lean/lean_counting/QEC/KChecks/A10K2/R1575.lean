import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6300 = true := by
  decide +kernel

theorem tot6300 : totK PA10K2 A10K2.t6300 = [0, 732941354179, 2130692069044, 1697389360499, 398652374899, 25715051306, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6301 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6301 = true := by
  decide +kernel

theorem tot6301 : totK PA10K2 A10K2.t6301 = [232865494112, 1145779245860, 2031357411236, 1314990389956, 222208198449, 6032141194, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6302 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6302 = true := by
  decide +kernel

theorem tot6302 : totK PA10K2 A10K2.t6302 = [613328696870, 1986851222271, 1858586187943, 531572741982, 39929742215, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6303 = true := by
  decide +kernel

theorem tot6303 : totK PA10K2 A10K2.t6303 = [0, 812481703954, 2293883908484, 1625883198594, 279208343189, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
