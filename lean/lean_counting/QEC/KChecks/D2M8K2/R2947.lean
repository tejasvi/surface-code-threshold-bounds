import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11788 = true := by
  decide +kernel

theorem tot11788 : totK PD2M8K2 D2M8K2.t11788 = [0, 183111027323, 471374068844, 257099046916, 22605955834, 0, 0, 0] := by
  decide +kernel

theorem rows11789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11789 = true := by
  decide +kernel

theorem tot11789 : totK PD2M8K2 D2M8K2.t11789 = [0, 175681360663, 472709082430, 244420151848, 13632511348, 0, 0, 0] := by
  decide +kernel

theorem rows11790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11790 = true := by
  decide +kernel

theorem tot11790 : totK PD2M8K2 D2M8K2.t11790 = [0, 0, 288077914132, 507562671323, 106389185785, 1164319620, 0, 0] := by
  decide +kernel

theorem rows11791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11791 = true := by
  decide +kernel

theorem tot11791 : totK PD2M8K2 D2M8K2.t11791 = [0, 0, 205790106697, 473698848182, 185383546352, 11885407614, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
