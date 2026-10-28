import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11796 = true := by
  decide +kernel

theorem tot11796 : totK PD2M8K2 D2M8K2.t11796 = [0, 185865977608, 446781365014, 246533235886, 22587877355, 0, 0, 0] := by
  decide +kernel

theorem rows11797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11797 = true := by
  decide +kernel

theorem tot11797 : totK PD2M8K2 D2M8K2.t11797 = [0, 177121157334, 481893162757, 232228324376, 10884111244, 0, 0, 0] := by
  decide +kernel

theorem rows11798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11798 = true := by
  decide +kernel

theorem tot11798 : totK PD2M8K2 D2M8K2.t11798 = [0, 0, 271000975469, 496267997314, 111291577257, 1240621948, 0, 0] := by
  decide +kernel

theorem rows11799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11799 = true := by
  decide +kernel

theorem tot11799 : totK PD2M8K2 D2M8K2.t11799 = [0, 0, 194655427550, 464630303054, 204893662865, 12488965933, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
