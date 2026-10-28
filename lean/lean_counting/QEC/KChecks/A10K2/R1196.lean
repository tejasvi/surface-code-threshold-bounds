import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4784 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4784 = true := by
  decide +kernel

theorem tot4784 : totK PA10K2 A10K2.t4784 = [0, 0, 465134454618, 1516369699994, 1759638351482, 782770303516, 150277059970, 6034215561, 0, 0] := by
  decide +kernel

theorem rows4785 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4785 = true := by
  decide +kernel

theorem tot4785 : totK PA10K2 A10K2.t4785 = [0, 0, 370867812652, 1759086406058, 2034856643399, 567614243168, 32742896604, 0, 0, 0] := by
  decide +kernel

theorem rows4786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4786 = true := by
  decide +kernel

theorem tot4786 : totK PA10K2 A10K2.t4786 = [0, 0, 0, 753696999872, 2289635495073, 1395658619782, 147638697404, 0, 0, 0] := by
  decide +kernel

theorem rows4787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4787 = true := by
  decide +kernel

theorem tot4787 : totK PA10K2 A10K2.t4787 = [0, 0, 0, 551129045159, 1983449291876, 1718333265199, 356202298536, 11740475125, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
