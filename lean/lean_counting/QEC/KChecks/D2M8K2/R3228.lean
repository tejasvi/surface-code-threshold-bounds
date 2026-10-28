import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12912 = true := by
  decide +kernel

theorem tot12912 : totK PD2M8K2 D2M8K2.t12912 = [0, 0, 220238803121, 492485773418, 171703304979, 4995066120, 0, 0] := by
  decide +kernel

theorem rows12913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12913 = true := by
  decide +kernel

theorem tot12913 : totK PD2M8K2 D2M8K2.t12913 = [0, 0, 155310982684, 477417327478, 240917314158, 11127237002, 0, 0] := by
  decide +kernel

theorem rows12914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12914 = true := by
  decide +kernel

theorem tot12914 : totK PD2M8K2 D2M8K2.t12914 = [0, 0, 201602959638, 465726662444, 203017771038, 12403393969, 0, 0] := by
  decide +kernel

theorem rows12915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12915 = true := by
  decide +kernel

theorem tot12915 : totK PD2M8K2 D2M8K2.t12915 = [0, 0, 194810237741, 492207847296, 201432854391, 3787589928, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
