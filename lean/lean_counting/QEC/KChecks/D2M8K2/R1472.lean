import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5888 = true := by
  decide +kernel

theorem tot5888 : totK PD2M8K2 D2M8K2.t5888 = [194676388760, 479299603045, 226582478317, 12244257065, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5889 = true := by
  decide +kernel

theorem tot5889 : totK PD2M8K2 D2M8K2.t5889 = [43115208482, 277592997856, 386468867764, 182096733456, 21396654552, 0, 0, 0] := by
  decide +kernel

theorem rows5890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5890 = true := by
  decide +kernel

theorem tot5890 : totK PD2M8K2 D2M8K2.t5890 = [0, 202460714931, 477999884752, 204664321360, 7994456143, 0, 0, 0] := by
  decide +kernel

theorem rows5891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5891 = true := by
  decide +kernel

theorem tot5891 : totK PD2M8K2 D2M8K2.t5891 = [77790425953, 250660471880, 375382941037, 179844262201, 8210597527, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
