import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t196 = true := by
  decide +kernel

theorem tot196 : totK PA10K2 A10K2.t196 = [0, 593578530300, 1792330027303, 1656289546858, 737271262006, 273151089637, 37674914273, 0, 0, 0] := by
  decide +kernel

theorem rows197 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t197 = true := by
  decide +kernel

theorem tot197 : totK PA10K2 A10K2.t197 = [0, 0, 760225405174, 2189913156548, 1701988274305, 386545547286, 25680132735, 0, 0, 0] := by
  decide +kernel

theorem rows198 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t198 = true := by
  decide +kernel

theorem tot198 : totK PA10K2 A10K2.t198 = [0, 475649046669, 1787718565190, 2072299737093, 768684551100, 70473210457, 0, 0, 0, 0] := by
  decide +kernel

theorem rows199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t199 = true := by
  decide +kernel

theorem tot199 : totK PA10K2 A10K2.t199 = [0, 317511839201, 1500310798531, 2203032161651, 968094386369, 83062694590, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
