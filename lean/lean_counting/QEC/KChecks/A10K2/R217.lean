import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows868 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t868 = true := by
  decide +kernel

theorem tot868 : totK PA10K2 A10K2.t868 = [42391554479, 545035604328, 1848628687769, 1955797132428, 524209752224, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

theorem rows869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t869 = true := by
  decide +kernel

theorem tot869 : totK PA10K2 A10K2.t869 = [438587663932, 1669559163132, 2010878297318, 797058744420, 60624008778, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows870 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t870 = true := by
  decide +kernel

theorem tot870 : totK PA10K2 A10K2.t870 = [489106248051, 1825549821856, 2039124123083, 617677341260, 43911329915, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows871 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t871 = true := by
  decide +kernel

theorem tot871 : totK PA10K2 A10K2.t871 = [121146523123, 1042270100062, 2200921930082, 1527873229772, 289854713105, 6851704726, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
