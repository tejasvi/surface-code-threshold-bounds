import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8184 = true := by
  decide +kernel

theorem tot8184 : totK PA10K2 A10K2.t8184 = [0, 0, 0, 0, 544821805588, 1948145895583, 1969963325636, 429683351399, 11699940467, 0] := by
  decide +kernel

theorem rows8185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8185 = true := by
  decide +kernel

theorem tot8185 : totK PA10K2 A10K2.t8185 = [0, 0, 0, 0, 0, 805322809803, 2236382998230, 1452157562239, 226113577431, 6318667960] := by
  decide +kernel

theorem rows8186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8186 = true := by
  decide +kernel

theorem tot8186 : totK PA10K2 A10K2.t8186 = [0, 0, 0, 0, 500120049515, 1682339437357, 1911741883731, 667860896635, 56636113972, 0] := by
  decide +kernel

theorem rows8187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8187 = true := by
  decide +kernel

theorem tot8187 : totK PA10K2 A10K2.t8187 = [0, 0, 0, 0, 254316147261, 1338098754876, 2164768235587, 1085162537337, 102980714170, 0] := by
  decide +kernel

end QECKChecks.A10K2
