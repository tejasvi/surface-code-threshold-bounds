import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9644 = true := by
  decide +kernel

theorem tot9644 : totK PD2M8K2 D2M8K2.t9644 = [0, 94311201580, 306793998148, 359714983729, 155996316296, 13468148062, 0, 0] := by
  decide +kernel

theorem rows9645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9645 = true := by
  decide +kernel

theorem tot9645 : totK PD2M8K2 D2M8K2.t9645 = [0, 181686402588, 452742399810, 242857138784, 20034711845, 0, 0, 0] := by
  decide +kernel

theorem rows9646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9646 = true := by
  decide +kernel

theorem tot9646 : totK PD2M8K2 D2M8K2.t9646 = [0, 163293401453, 467356015483, 264033483993, 26647743515, 0, 0, 0] := by
  decide +kernel

theorem rows9647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9647 = true := by
  decide +kernel

theorem tot9647 : totK PD2M8K2 D2M8K2.t9647 = [0, 0, 174801926414, 444529556760, 250600707032, 25330798048, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
