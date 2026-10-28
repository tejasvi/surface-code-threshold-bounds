import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t792 = true := by
  decide +kernel

theorem tot792 : totK PD2M8K2 D2M8K2.t792 = [0, 0, 161632672595, 448654069602, 269936793698, 21167182954, 0, 0] := by
  decide +kernel

theorem rows793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t793 = true := by
  decide +kernel

theorem tot793 : totK PD2M8K2 D2M8K2.t793 = [0, 10096136370, 176439092139, 464350301256, 225468305720, 9315544859, 0, 0] := by
  decide +kernel

theorem rows794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t794 = true := by
  decide +kernel

theorem tot794 : totK PD2M8K2 D2M8K2.t794 = [0, 190584765103, 464383880492, 245386150780, 23211205057, 0, 0, 0] := by
  decide +kernel

theorem rows795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t795 = true := by
  decide +kernel

theorem tot795 : totK PD2M8K2 D2M8K2.t795 = [0, 186831124661, 473078995982, 223362474787, 12426737048, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
