import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1908 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1908 = true := by
  decide +kernel

theorem tot1908 : totK PA10K2 A10K2.t1908 = [0, 306766947263, 1497952622526, 2232042027340, 953433518543, 86580489483, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1909 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1909 = true := by
  decide +kernel

theorem tot1909 : totK PA10K2 A10K2.t1909 = [0, 237116228581, 1053565578541, 1910958337540, 1431802579424, 325040370860, 13349922262, 0, 0, 0] := by
  decide +kernel

theorem rows1910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1910 = true := by
  decide +kernel

theorem tot1910 : totK PA10K2 A10K2.t1910 = [0, 540850438005, 1925814805980, 1939971374320, 535261360348, 32780555804, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1911 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1911 = true := by
  decide +kernel

theorem tot1911 : totK PA10K2 A10K2.t1911 = [0, 0, 732874990255, 2117604802742, 1682562046471, 395169172083, 25715051306, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
