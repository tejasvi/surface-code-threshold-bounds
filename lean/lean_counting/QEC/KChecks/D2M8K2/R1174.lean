import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4696 = true := by
  decide +kernel

theorem tot4696 : totK PD2M8K2 D2M8K2.t4696 = [0, 0, 212205468179, 496273625632, 181621806743, 6157715822, 0, 0] := by
  decide +kernel

theorem rows4697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4697 = true := by
  decide +kernel

theorem tot4697 : totK PD2M8K2 D2M8K2.t4697 = [0, 0, 175118618402, 450165616471, 261020903715, 29320587420, 0, 0] := by
  decide +kernel

theorem rows4698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4698 = true := by
  decide +kernel

theorem tot4698 : totK PD2M8K2 D2M8K2.t4698 = [0, 0, 173685690905, 459497671115, 264127809627, 18752432391, 0, 0] := by
  decide +kernel

theorem rows4699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4699 = true := by
  decide +kernel

theorem tot4699 : totK PD2M8K2 D2M8K2.t4699 = [0, 0, 176191278966, 470967896172, 257989844751, 16955927158, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
