import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows308 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t308 = true := by
  decide +kernel

theorem tot308 : totK PA10K2 A10K2.t308 = [0, 0, 541007009248, 1794369303945, 1800082441731, 549769733111, 47811729153, 0, 0, 0] := by
  decide +kernel

theorem rows309 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t309 = true := by
  decide +kernel

theorem tot309 : totK PA10K2 A10K2.t309 = [0, 0, 216529667229, 1455806719816, 2200856291900, 770798034640, 45791150720, 0, 0, 0] := by
  decide +kernel

theorem rows310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t310 = true := by
  decide +kernel

theorem tot310 : totK PA10K2 A10K2.t310 = [0, 0, 295157913241, 1245774859868, 1945504807743, 1040489553323, 173387221522, 5546304973, 0, 0] := by
  decide +kernel

theorem rows311 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t311 = true := by
  decide +kernel

theorem tot311 : totK PA10K2 A10K2.t311 = [0, 293929698888, 1190014462480, 1770500952073, 1375340811523, 440242193272, 29791859037, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
