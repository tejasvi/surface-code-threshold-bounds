import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2996 = true := by
  decide +kernel

theorem tot2996 : totK PA10K2 A10K2.t2996 = [0, 0, 444019298193, 1622553303028, 1991379904734, 764583587497, 68815120782, 0, 0, 0] := by
  decide +kernel

theorem rows2997 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2997 = true := by
  decide +kernel

theorem tot2997 : totK PA10K2 A10K2.t2997 = [0, 0, 339775201887, 1586575271412, 2096547894882, 859632309063, 76359375511, 0, 0, 0] := by
  decide +kernel

theorem rows2998 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2998 = true := by
  decide +kernel

theorem tot2998 : totK PA10K2 A10K2.t2998 = [0, 0, 111865401186, 855744280856, 2118529216847, 1522513398165, 265210313109, 6904928264, 0, 0] := by
  decide +kernel

theorem rows2999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2999 = true := by
  decide +kernel

theorem tot2999 : totK PA10K2 A10K2.t2999 = [0, 0, 481669913317, 1850862214599, 2078440211517, 639189776606, 25587960981, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
