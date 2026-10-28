import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10028 = true := by
  decide +kernel

theorem tot10028 : totK PD2M8K2 D2M8K2.t10028 = [0, 182755202180, 459954354251, 270233866782, 28085085008, 0, 0, 0] := by
  decide +kernel

theorem rows10029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10029 = true := by
  decide +kernel

theorem tot10029 : totK PD2M8K2 D2M8K2.t10029 = [0, 173317023195, 466621991148, 243630564502, 12644583987, 0, 0, 0] := by
  decide +kernel

theorem rows10030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10030 = true := by
  decide +kernel

theorem tot10030 : totK PD2M8K2 D2M8K2.t10030 = [0, 0, 260024104385, 504312078716, 138791999320, 2324332710, 0, 0] := by
  decide +kernel

theorem rows10031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10031 = true := by
  decide +kernel

theorem tot10031 : totK PD2M8K2 D2M8K2.t10031 = [0, 46925638102, 238012347925, 414110707659, 161434884589, 10870367030, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
