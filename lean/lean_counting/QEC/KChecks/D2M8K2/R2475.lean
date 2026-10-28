import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9900 = true := by
  decide +kernel

theorem tot9900 : totK PD2M8K2 D2M8K2.t9900 = [0, 166296197476, 452289957764, 273654773098, 28176604845, 0, 0, 0] := by
  decide +kernel

theorem rows9901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9901 = true := by
  decide +kernel

theorem tot9901 : totK PD2M8K2 D2M8K2.t9901 = [0, 159593600675, 434038672718, 284855583791, 29920750807, 0, 0, 0] := by
  decide +kernel

theorem rows9902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9902 = true := by
  decide +kernel

theorem tot9902 : totK PD2M8K2 D2M8K2.t9902 = [0, 89392755611, 354285068278, 375568775736, 74855122081, 1198073392, 0, 0] := by
  decide +kernel

theorem rows9903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9903 = true := by
  decide +kernel

theorem tot9903 : totK PD2M8K2 D2M8K2.t9903 = [0, 0, 239037119014, 487090172084, 165216619008, 8466643012, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
