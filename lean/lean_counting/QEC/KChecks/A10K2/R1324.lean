import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5296 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5296 = true := by
  decide +kernel

theorem tot5296 : totK PA10K2 A10K2.t5296 = [0, 0, 192096356431, 1348008389394, 2231403620133, 921134092748, 66528807994, 0, 0, 0] := by
  decide +kernel

theorem rows5297 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5297 = true := by
  decide +kernel

theorem tot5297 : totK PA10K2 A10K2.t5297 = [0, 0, 293349203532, 1191587535868, 1842716052781, 1145138751115, 228179536165, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5298 = true := by
  decide +kernel

theorem tot5298 : totK PA10K2 A10K2.t5298 = [0, 0, 258963577619, 1349513289411, 2198236873370, 1044567354666, 91903596134, 0, 0, 0] := by
  decide +kernel

theorem rows5299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5299 = true := by
  decide +kernel

theorem tot5299 : totK PA10K2 A10K2.t5299 = [0, 0, 303055287478, 1274585393495, 1922009424880, 1182596626871, 220344861941, 6853348008, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
