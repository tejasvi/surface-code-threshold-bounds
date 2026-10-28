import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6720 = true := by
  decide +kernel

theorem tot6720 : totK PD2M8K2 D2M8K2.t6720 = [0, 0, 216215700994, 485006354917, 168538335950, 5139136978, 0, 0] := by
  decide +kernel

theorem rows6721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6721 = true := by
  decide +kernel

theorem tot6721 : totK PD2M8K2 D2M8K2.t6721 = [0, 0, 183923289778, 459539879829, 220683578781, 18069584445, 0, 0] := by
  decide +kernel

theorem rows6722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6722 = true := by
  decide +kernel

theorem tot6722 : totK PD2M8K2 D2M8K2.t6722 = [0, 0, 201556034178, 485463279270, 182268770551, 5187627908, 0, 0] := by
  decide +kernel

theorem rows6723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6723 = true := by
  decide +kernel

theorem tot6723 : totK PD2M8K2 D2M8K2.t6723 = [0, 0, 174671112157, 447891318789, 242120078674, 22801359543, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
