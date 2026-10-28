import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11932 = true := by
  decide +kernel

theorem tot11932 : totK PD2M8K2 D2M8K2.t11932 = [0, 0, 302017108546, 486585804930, 112529908817, 1238673482, 0, 0] := by
  decide +kernel

theorem rows11933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11933 = true := by
  decide +kernel

theorem tot11933 : totK PD2M8K2 D2M8K2.t11933 = [78840680958, 114310399466, 138909030290, 370045186487, 164917271958, 8063697217, 0, 0] := by
  decide +kernel

theorem rows11934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11934 = true := by
  decide +kernel

theorem tot11934 : totK PD2M8K2 D2M8K2.t11934 = [161237636129, 470148130122, 240131177306, 14438114664, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11935 = true := by
  decide +kernel

theorem tot11935 : totK PD2M8K2 D2M8K2.t11935 = [169463558916, 451143397694, 242219595961, 14298627569, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
