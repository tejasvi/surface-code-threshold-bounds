import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2904 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2904 = true := by
  decide +kernel

theorem tot2904 : totK PA10K2 A10K2.t2904 = [507610568542, 1755939365136, 1862198747948, 706655776026, 127166762327, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2905 = true := by
  decide +kernel

theorem tot2905 : totK PA10K2 A10K2.t2905 = [322051627922, 1512024685067, 2232897585318, 1039824931313, 106572156292, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2906 = true := by
  decide +kernel

theorem tot2906 : totK PA10K2 A10K2.t2906 = [0, 613484598660, 2057173817647, 1929381070947, 436811728128, 13814447077, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2907 = true := by
  decide +kernel

theorem tot2907 : totK PA10K2 A10K2.t2907 = [0, 311873932364, 1500611188146, 2134516017991, 863445776040, 75643137603, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
