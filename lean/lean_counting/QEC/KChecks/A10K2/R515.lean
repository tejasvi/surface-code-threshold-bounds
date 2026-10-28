import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2060 = true := by
  decide +kernel

theorem tot2060 : totK PA10K2 A10K2.t2060 = [312105522993, 1312022374349, 2029350179747, 1213338927403, 225467403976, 14423867395, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2061 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2061 = true := by
  decide +kernel

theorem tot2061 : totK PA10K2 A10K2.t2061 = [505112952595, 1867308025672, 1982348598108, 560284403325, 32780555804, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2062 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2062 = true := by
  decide +kernel

theorem tot2062 : totK PA10K2 A10K2.t2062 = [0, 672713728931, 2120109129211, 1766691056311, 414137539969, 25715051306, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2063 = true := by
  decide +kernel

theorem tot2063 : totK PA10K2 A10K2.t2063 = [223542980710, 1123359632691, 1964937972235, 1297979284219, 219257644869, 6032141194, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
