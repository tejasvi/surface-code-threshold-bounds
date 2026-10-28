import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4472 = true := by
  decide +kernel

theorem tot4472 : totK PD2M8K2 D2M8K2.t4472 = [0, 156375446972, 411686460064, 322986477444, 39345943856, 0, 0, 0] := by
  decide +kernel

theorem rows4473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4473 = true := by
  decide +kernel

theorem tot4473 : totK PD2M8K2 D2M8K2.t4473 = [0, 192733271514, 465174746117, 232369998595, 15764060008, 0, 0, 0] := by
  decide +kernel

theorem rows4474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4474 = true := by
  decide +kernel

theorem tot4474 : totK PD2M8K2 D2M8K2.t4474 = [0, 70523670977, 374886409266, 373161036199, 93804771224, 12086244250, 0, 0] := by
  decide +kernel

theorem rows4475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4475 = true := by
  decide +kernel

theorem tot4475 : totK PD2M8K2 D2M8K2.t4475 = [0, 0, 167366882782, 462619066671, 251936643557, 16149348738, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
