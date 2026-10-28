import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows624 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t624 = true := by
  decide +kernel

theorem tot624 : totK PA10K2 A10K2.t624 = [0, 509805898549, 1880564582939, 2060493957975, 655715006689, 44386085507, 0, 0, 0, 0] := by
  decide +kernel

theorem rows625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t625 = true := by
  decide +kernel

theorem tot625 : totK PA10K2 A10K2.t625 = [0, 0, 653664456442, 2180157828835, 1919252548147, 374586757438, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t626 = true := by
  decide +kernel

theorem tot626 : totK PA10K2 A10K2.t626 = [0, 0, 554864361874, 1816703998489, 1897530999251, 668231911335, 55871919474, 0, 0, 0] := by
  decide +kernel

theorem rows627 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t627 = true := by
  decide +kernel

theorem tot627 : totK PA10K2 A10K2.t627 = [0, 0, 566661513637, 1932722226185, 1917587144003, 507624026736, 31080743953, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
