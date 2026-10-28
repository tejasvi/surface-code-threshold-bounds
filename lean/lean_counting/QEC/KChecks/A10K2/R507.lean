import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2028 = true := by
  decide +kernel

theorem tot2028 : totK PA10K2 A10K2.t2028 = [0, 0, 0, 328627686157, 1524133331801, 2154001111472, 884835525002, 68645789942, 0, 0] := by
  decide +kernel

theorem rows2029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2029 = true := by
  decide +kernel

theorem tot2029 : totK PA10K2 A10K2.t2029 = [0, 0, 0, 0, 596006246744, 1998165833985, 1856095795998, 391325559329, 12132367858, 0] := by
  decide +kernel

theorem rows2030 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2030 = true := by
  decide +kernel

theorem tot2030 : totK PA10K2 A10K2.t2030 = [322245181260, 1097486800689, 1116364296576, 349250536676, 26491486257, 447704699636, 1025234692155, 501217979401, 48886019071, 0] := by
  decide +kernel

theorem rows2031 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2031 = true := by
  decide +kernel

theorem tot2031 : totK PA10K2 A10K2.t2031 = [554005531953, 1983232489538, 1920786732666, 439582491487, 11006402110, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
