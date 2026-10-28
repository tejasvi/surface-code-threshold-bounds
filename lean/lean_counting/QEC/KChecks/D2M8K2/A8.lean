import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A7

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows9596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9596 = true := by
  rw [show D2M8K2.u9596 = KTree.node D2M8K2.t9600 (nat_lit 20636741) (nat_lit 1397288342) (nat_lit 0) D2M8K2.t9601 from rfl, allE_node, rows9600, irow9596, rows9601]
  all_goals rfl

theorem atot9596 : totK PD2M8K2 D2M8K2.u9596 = [0, 348552953130, 936337480219, 508039243520, 37669907889, 0, 0, 0] := by
  rw [show D2M8K2.u9596 = KTree.node D2M8K2.t9600 (nat_lit 20636741) (nat_lit 1397288342) (nat_lit 0) D2M8K2.t9601 from rfl, totK_node, tot9600, tot9601]
  decide +kernel

theorem arows9597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9597 = true := by
  rw [show D2M8K2.u9597 = KTree.node D2M8K2.t9602 (nat_lit 20639754) (nat_lit 3596347437) (nat_lit 0) D2M8K2.t9603 from rfl, allE_node, rows9602, irow9597, rows9603]
  all_goals rfl

theorem atot9597 : totK PD2M8K2 D2M8K2.u9597 = [0, 347594180315, 896390365903, 487712855802, 42291310187, 0, 0, 0] := by
  rw [show D2M8K2.u9597 = KTree.node D2M8K2.t9602 (nat_lit 20639754) (nat_lit 3596347437) (nat_lit 0) D2M8K2.t9603 from rfl, totK_node, tot9602, tot9603]
  decide +kernel

theorem arows9599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9599 = true := by
  rw [show D2M8K2.u9599 = KTree.node D2M8K2.t9604 (nat_lit 20641536) (nat_lit 3682757930) (nat_lit 0) D2M8K2.t9605 from rfl, allE_node, rows9604, irow9599, rows9605]
  all_goals rfl

theorem atot9599 : totK PD2M8K2 D2M8K2.u9599 = [0, 109630231560, 637996708011, 832111973506, 177063737304, 4879840392, 0, 0] := by
  rw [show D2M8K2.u9599 = KTree.node D2M8K2.t9604 (nat_lit 20641536) (nat_lit 3682757930) (nat_lit 0) D2M8K2.t9605 from rfl, totK_node, tot9604, tot9605]
  decide +kernel

theorem arows9600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9600 = true := by
  rw [show D2M8K2.u9600 = KTree.node D2M8K2.t9606 (nat_lit 20643657) (nat_lit 1835221234) (nat_lit 0) D2M8K2.t9607 from rfl, allE_node, rows9606, irow9600, rows9607]
  all_goals rfl

theorem atot9600 : totK PD2M8K2 D2M8K2.u9600 = [0, 364512660405, 933817721339, 480696119545, 34321553673, 0, 0, 0] := by
  rw [show D2M8K2.u9600 = KTree.node D2M8K2.t9606 (nat_lit 20643657) (nat_lit 1835221234) (nat_lit 0) D2M8K2.t9607 from rfl, totK_node, tot9606, tot9607]
  decide +kernel

theorem arows9603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9603 = true := by
  rw [show D2M8K2.u9603 = KTree.node D2M8K2.t9608 (nat_lit 20645404) (nat_lit 2875738752) (nat_lit 0) D2M8K2.t9609 from rfl, allE_node, rows9608, irow9603, rows9609]
  all_goals rfl

theorem atot9603 : totK PD2M8K2 D2M8K2.u9603 = [0, 86757284321, 643462068543, 841764833958, 181911107458, 4931404646, 0, 0] := by
  rw [show D2M8K2.u9603 = KTree.node D2M8K2.t9608 (nat_lit 20645404) (nat_lit 2875738752) (nat_lit 0) D2M8K2.t9609 from rfl, totK_node, tot9608, tot9609]
  decide +kernel

theorem arows9604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9604 = true := by
  rw [show D2M8K2.u9604 = KTree.node D2M8K2.t9610 (nat_lit 20650385) (nat_lit 2089390254) (nat_lit 0) D2M8K2.t9611 from rfl, allE_node, rows9610, irow9604, rows9611]
  all_goals rfl

theorem atot9604 : totK PD2M8K2 D2M8K2.u9604 = [0, 358713055222, 937080414407, 506215448799, 35231247285, 0, 0, 0] := by
  rw [show D2M8K2.u9604 = KTree.node D2M8K2.t9610 (nat_lit 20650385) (nat_lit 2089390254) (nat_lit 0) D2M8K2.t9611 from rfl, totK_node, tot9610, tot9611]
  decide +kernel

theorem arows9606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9606 = true := by
  rw [show D2M8K2.u9606 = KTree.node D2M8K2.t9612 (nat_lit 20652047) (nat_lit 2771375578) (nat_lit 0) D2M8K2.t9613 from rfl, allE_node, rows9612, irow9606, rows9613]
  all_goals rfl

theorem atot9606 : totK PD2M8K2 D2M8K2.u9606 = [0, 0, 458992789191, 972218373470, 311459457416, 9650085089, 0, 0] := by
  rw [show D2M8K2.u9606 = KTree.node D2M8K2.t9612 (nat_lit 20652047) (nat_lit 2771375578) (nat_lit 0) D2M8K2.t9613 from rfl, totK_node, tot9612, tot9613]
  decide +kernel

theorem arows9607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9607 = true := by
  rw [show D2M8K2.u9607 = KTree.node D2M8K2.t9614 (nat_lit 20653877) (nat_lit 2308593483) (nat_lit 0) D2M8K2.t9615 from rfl, allE_node, rows9614, irow9607, rows9615]
  all_goals rfl

theorem atot9607 : totK PD2M8K2 D2M8K2.u9607 = [0, 352300513259, 879815298096, 438848436553, 86497845749, 12101082977, 0, 0] := by
  rw [show D2M8K2.u9607 = KTree.node D2M8K2.t9614 (nat_lit 20653877) (nat_lit 2308593483) (nat_lit 0) D2M8K2.t9615 from rfl, totK_node, tot9614, tot9615]
  decide +kernel

theorem arows9611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9611 = true := by
  rw [show D2M8K2.u9611 = KTree.node D2M8K2.t9616 (nat_lit 20655394) (nat_lit 3782462708) (nat_lit 0) D2M8K2.t9617 from rfl, allE_node, rows9616, irow9611, rows9617]
  all_goals rfl

theorem atot9611 : totK PD2M8K2 D2M8K2.u9611 = [0, 99653540325, 680223972103, 883855803536, 151707906874, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9611 = KTree.node D2M8K2.t9616 (nat_lit 20655394) (nat_lit 3782462708) (nat_lit 0) D2M8K2.t9617 from rfl, totK_node, tot9616, tot9617]
  decide +kernel

theorem arows9612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9612 = true := by
  rw [show D2M8K2.u9612 = KTree.node D2M8K2.t9618 (nat_lit 20660683) (nat_lit 1394712465) (nat_lit 0) D2M8K2.t9619 from rfl, allE_node, rows9618, irow9612, rows9619]
  all_goals rfl

theorem atot9612 : totK PD2M8K2 D2M8K2.u9612 = [0, 359096659849, 920683581799, 470569329508, 34503428373, 0, 0, 0] := by
  rw [show D2M8K2.u9612 = KTree.node D2M8K2.t9618 (nat_lit 20660683) (nat_lit 1394712465) (nat_lit 0) D2M8K2.t9619 from rfl, totK_node, tot9618, tot9619]
  decide +kernel

theorem arows9614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9614 = true := by
  rw [show D2M8K2.u9614 = KTree.node D2M8K2.t9620 (nat_lit 20662445) (nat_lit 1598316346) (nat_lit 0) D2M8K2.t9621 from rfl, allE_node, rows9620, irow9614, rows9621]
  all_goals rfl

theorem atot9614 : totK PD2M8K2 D2M8K2.u9614 = [0, 87204366028, 613796891022, 868135014470, 208393131356, 5172807878, 0, 0] := by
  rw [show D2M8K2.u9614 = KTree.node D2M8K2.t9620 (nat_lit 20662445) (nat_lit 1598316346) (nat_lit 0) D2M8K2.t9621 from rfl, totK_node, tot9620, tot9621]
  decide +kernel

theorem arows9615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9615 = true := by
  rw [show D2M8K2.u9615 = KTree.node D2M8K2.t9622 (nat_lit 20664603) (nat_lit 2701248313) (nat_lit 0) D2M8K2.t9623 from rfl, allE_node, rows9622, irow9615, rows9623]
  all_goals rfl

theorem atot9615 : totK PD2M8K2 D2M8K2.u9615 = [0, 327282852593, 892029334101, 542473746325, 46965148540, 0, 0, 0] := by
  rw [show D2M8K2.u9615 = KTree.node D2M8K2.t9622 (nat_lit 20664603) (nat_lit 2701248313) (nat_lit 0) D2M8K2.t9623 from rfl, totK_node, tot9622, tot9623]
  decide +kernel

theorem arows9618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9618 = true := by
  rw [show D2M8K2.u9618 = KTree.node D2M8K2.t9624 (nat_lit 20666317) (nat_lit 1275754405) (nat_lit 0) D2M8K2.t9625 from rfl, allE_node, rows9624, irow9618, rows9625]
  all_goals rfl

theorem atot9618 : totK PD2M8K2 D2M8K2.u9618 = [0, 122477021425, 625643102975, 825245906150, 208877681251, 5228939780, 0, 0] := by
  rw [show D2M8K2.u9618 = KTree.node D2M8K2.t9624 (nat_lit 20666317) (nat_lit 1275754405) (nat_lit 0) D2M8K2.t9625 from rfl, totK_node, tot9624, tot9625]
  decide +kernel

theorem arows9619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9619 = true := by
  rw [show D2M8K2.u9619 = KTree.node D2M8K2.t9626 (nat_lit 20668140) (nat_lit 3185297290) (nat_lit 0) D2M8K2.t9627 from rfl, allE_node, rows9626, irow9619, rows9627]
  all_goals rfl

theorem atot9619 : totK PD2M8K2 D2M8K2.u9619 = [0, 201096944435, 769021704554, 685229182563, 96899424870, 1096505104, 0, 0] := by
  rw [show D2M8K2.u9619 = KTree.node D2M8K2.t9626 (nat_lit 20668140) (nat_lit 3185297290) (nat_lit 0) D2M8K2.t9627 from rfl, totK_node, tot9626, tot9627]
  decide +kernel

theorem arows9621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9621 = true := by
  rw [show D2M8K2.u9621 = KTree.node D2M8K2.t9628 (nat_lit 20670801) (nat_lit 1282791063) (nat_lit 0) D2M8K2.t9629 from rfl, allE_node, rows9628, irow9621, rows9629]
  all_goals rfl

theorem atot9621 : totK PD2M8K2 D2M8K2.u9621 = [0, 332836782526, 883455201572, 536663331417, 47307690931, 0, 0, 0] := by
  rw [show D2M8K2.u9621 = KTree.node D2M8K2.t9628 (nat_lit 20670801) (nat_lit 1282791063) (nat_lit 0) D2M8K2.t9629 from rfl, totK_node, tot9628, tot9629]
  decide +kernel

theorem arows9622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9622 = true := by
  rw [show D2M8K2.u9622 = KTree.node D2M8K2.t9630 (nat_lit 20672257) (nat_lit 1457256795) (nat_lit 0) D2M8K2.t9631 from rfl, allE_node, rows9630, irow9622, rows9631]
  all_goals rfl

theorem atot9622 : totK PD2M8K2 D2M8K2.u9622 = [0, 92937627352, 618800226085, 856208040742, 209700649456, 4901932702, 0, 0] := by
  rw [show D2M8K2.u9622 = KTree.node D2M8K2.t9630 (nat_lit 20672257) (nat_lit 1457256795) (nat_lit 0) D2M8K2.t9631 from rfl, totK_node, tot9630, tot9631]
  decide +kernel

theorem arows9627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9627 = true := by
  rw [show D2M8K2.u9627 = KTree.node D2M8K2.t9632 (nat_lit 20673922) (nat_lit 4124157814) (nat_lit 0) D2M8K2.t9633 from rfl, allE_node, rows9632, irow9627, rows9633]
  all_goals rfl

theorem atot9627 : totK PD2M8K2 D2M8K2.u9627 = [0, 0, 374050043120, 947102629224, 419144377517, 23543553825, 0, 0] := by
  rw [show D2M8K2.u9627 = KTree.node D2M8K2.t9632 (nat_lit 20673922) (nat_lit 4124157814) (nat_lit 0) D2M8K2.t9633 from rfl, totK_node, tot9632, tot9633]
  decide +kernel

theorem arows9628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9628 = true := by
  rw [show D2M8K2.u9628 = KTree.node D2M8K2.t9634 (nat_lit 20675499) (nat_lit 2320033674) (nat_lit 0) D2M8K2.t9635 from rfl, allE_node, rows9634, irow9628, rows9635]
  all_goals rfl

theorem atot9628 : totK PD2M8K2 D2M8K2.u9628 = [0, 0, 168849847679, 755172804541, 676568134825, 102395077616, 1369150432, 0] := by
  rw [show D2M8K2.u9628 = KTree.node D2M8K2.t9634 (nat_lit 20675499) (nat_lit 2320033674) (nat_lit 0) D2M8K2.t9635 from rfl, totK_node, tot9634, tot9635]
  decide +kernel

theorem arows9630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9630 = true := by
  rw [show D2M8K2.u9630 = KTree.node D2M8K2.t9636 (nat_lit 20681131) (nat_lit 1082211123) (nat_lit 0) D2M8K2.t9637 from rfl, allE_node, rows9636, irow9630, rows9637]
  all_goals rfl

theorem atot9630 : totK PD2M8K2 D2M8K2.u9630 = [0, 0, 328200094643, 918490173656, 470413245550, 25099559326, 0, 0] := by
  rw [show D2M8K2.u9630 = KTree.node D2M8K2.t9636 (nat_lit 20681131) (nat_lit 1082211123) (nat_lit 0) D2M8K2.t9637 from rfl, totK_node, tot9636, tot9637]
  decide +kernel

theorem arows9631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9631 = true := by
  rw [show D2M8K2.u9631 = KTree.node D2M8K2.t9638 (nat_lit 20684568) (nat_lit 2827701208) (nat_lit 0) D2M8K2.t9639 from rfl, allE_node, rows9638, irow9631, rows9639]
  all_goals rfl

theorem atot9631 : totK PD2M8K2 D2M8K2.u9631 = [0, 0, 378704205691, 970070188383, 409529910843, 16674219220, 0, 0] := by
  rw [show D2M8K2.u9631 = KTree.node D2M8K2.t9638 (nat_lit 20684568) (nat_lit 2827701208) (nat_lit 0) D2M8K2.t9639 from rfl, totK_node, tot9638, tot9639]
  decide +kernel

theorem arows9634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9634 = true := by
  rw [show D2M8K2.u9634 = KTree.node D2M8K2.t9640 (nat_lit 20688202) (nat_lit 3480518199) (nat_lit 0) D2M8K2.t9641 from rfl, allE_node, rows9640, irow9634, rows9641]
  all_goals rfl

theorem atot9634 : totK PD2M8K2 D2M8K2.u9634 = [0, 0, 410228495996, 980014774669, 354471540243, 12463624165, 0, 0] := by
  rw [show D2M8K2.u9634 = KTree.node D2M8K2.t9640 (nat_lit 20688202) (nat_lit 3480518199) (nat_lit 0) D2M8K2.t9641 from rfl, totK_node, tot9640, tot9641]
  decide +kernel

theorem arows9635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9635 = true := by
  rw [show D2M8K2.u9635 = KTree.node D2M8K2.t9642 (nat_lit 20691642) (nat_lit 3241835309) (nat_lit 0) D2M8K2.t9643 from rfl, allE_node, rows9642, irow9635, rows9643]
  all_goals rfl

theorem atot9635 : totK PD2M8K2 D2M8K2.u9635 = [0, 0, 361767879591, 953217239904, 424137813106, 17173502218, 0, 0] := by
  rw [show D2M8K2.u9635 = KTree.node D2M8K2.t9642 (nat_lit 20691642) (nat_lit 3241835309) (nat_lit 0) D2M8K2.t9643 from rfl, totK_node, tot9642, tot9643]
  decide +kernel

theorem arows9637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9637 = true := by
  rw [show D2M8K2.u9637 = KTree.node D2M8K2.t9644 (nat_lit 20698550) (nat_lit 3945465005) (nat_lit 0) D2M8K2.t9645 from rfl, allE_node, rows9644, irow9637, rows9645]
  all_goals rfl

theorem atot9637 : totK PD2M8K2 D2M8K2.u9637 = [0, 275997604168, 759536397958, 606517587518, 176031028141, 13468148062, 0, 0] := by
  rw [show D2M8K2.u9637 = KTree.node D2M8K2.t9644 (nat_lit 20698550) (nat_lit 3945465005) (nat_lit 0) D2M8K2.t9645 from rfl, totK_node, tot9644, tot9645]
  decide +kernel

theorem arows9638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9638 = true := by
  rw [show D2M8K2.u9638 = KTree.node D2M8K2.t9646 (nat_lit 20700051) (nat_lit 3716614309) (nat_lit 0) D2M8K2.t9647 from rfl, allE_node, rows9646, irow9638, rows9647]
  all_goals rfl

theorem atot9638 : totK PD2M8K2 D2M8K2.u9638 = [0, 163293401453, 642157941897, 712279655062, 277248450547, 25330798048, 0, 0] := by
  rw [show D2M8K2.u9638 = KTree.node D2M8K2.t9646 (nat_lit 20700051) (nat_lit 3716614309) (nat_lit 0) D2M8K2.t9647 from rfl, totK_node, tot9646, tot9647]
  decide +kernel

theorem arows9642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9642 = true := by
  rw [show D2M8K2.u9642 = KTree.node D2M8K2.t9648 (nat_lit 20701234) (nat_lit 4005483109) (nat_lit 0) D2M8K2.t9649 from rfl, allE_node, rows9648, irow9642, rows9649]
  all_goals rfl

theorem atot9642 : totK PD2M8K2 D2M8K2.u9642 = [0, 142385201976, 567498308491, 794659585597, 306478414580, 12169858900, 0, 0] := by
  rw [show D2M8K2.u9642 = KTree.node D2M8K2.t9648 (nat_lit 20701234) (nat_lit 4005483109) (nat_lit 0) D2M8K2.t9649 from rfl, totK_node, tot9648, tot9649]
  decide +kernel

theorem arows9643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9643 = true := by
  rw [show D2M8K2.u9643 = KTree.node D2M8K2.t9650 (nat_lit 20702906) (nat_lit 4213924965) (nat_lit 0) D2M8K2.t9651 from rfl, allE_node, rows9650, irow9643, rows9651]
  all_goals rfl

theorem atot9643 : totK PD2M8K2 D2M8K2.u9643 = [0, 243105295171, 805404113455, 657753573916, 101118350253, 1129489618, 0, 0] := by
  rw [show D2M8K2.u9643 = KTree.node D2M8K2.t9650 (nat_lit 20702906) (nat_lit 4213924965) (nat_lit 0) D2M8K2.t9651 from rfl, totK_node, tot9650, tot9651]
  decide +kernel

theorem arows9645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9645 = true := by
  rw [show D2M8K2.u9645 = KTree.node D2M8K2.t9652 (nat_lit 20704728) (nat_lit 3482285445) (nat_lit 0) D2M8K2.t9653 from rfl, allE_node, rows9652, irow9645, rows9653]
  all_goals rfl

theorem atot9645 : totK PD2M8K2 D2M8K2.u9645 = [0, 178868128735, 668463845136, 754199142506, 202959365765, 7938259948, 0, 0] := by
  rw [show D2M8K2.u9645 = KTree.node D2M8K2.t9652 (nat_lit 20704728) (nat_lit 3482285445) (nat_lit 0) D2M8K2.t9653 from rfl, totK_node, tot9652, tot9653]
  decide +kernel

theorem arows9646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9646 = true := by
  rw [show D2M8K2.u9646 = KTree.node D2M8K2.t9654 (nat_lit 20706401) (nat_lit 2121250605) (nat_lit 0) D2M8K2.t9655 from rfl, allE_node, rows9654, irow9646, rows9655]
  all_goals rfl

theorem atot9646 : totK PD2M8K2 D2M8K2.u9646 = [0, 234965345132, 808945964591, 662595788840, 106900447437, 1161838861, 0, 0] := by
  rw [show D2M8K2.u9646 = KTree.node D2M8K2.t9654 (nat_lit 20706401) (nat_lit 2121250605) (nat_lit 0) D2M8K2.t9655 from rfl, totK_node, tot9654, tot9655]
  decide +kernel

theorem arows9649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9649 = true := by
  rw [show D2M8K2.u9649 = KTree.node D2M8K2.t9656 (nat_lit 20708138) (nat_lit 4027463345) (nat_lit 0) D2M8K2.t9657 from rfl, allE_node, rows9656, irow9649, rows9657]
  all_goals rfl

theorem atot9649 : totK PD2M8K2 D2M8K2.u9649 = [0, 158714876269, 638853781701, 792804211435, 221415261973, 8017150856, 0, 0] := by
  rw [show D2M8K2.u9649 = KTree.node D2M8K2.t9656 (nat_lit 20708138) (nat_lit 4027463345) (nat_lit 0) D2M8K2.t9657 from rfl, totK_node, tot9656, tot9657]
  decide +kernel

theorem arows9650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9650 = true := by
  rw [show D2M8K2.u9650 = KTree.node D2M8K2.t9658 (nat_lit 20710424) (nat_lit 3743748224) (nat_lit 0) D2M8K2.t9659 from rfl, allE_node, rows9658, irow9650, rows9659]
  all_goals rfl

theorem atot9650 : totK PD2M8K2 D2M8K2.u9650 = [0, 171189201866, 777118894438, 766878005311, 113836619569, 0, 0, 0] := by
  rw [show D2M8K2.u9650 = KTree.node D2M8K2.t9658 (nat_lit 20710424) (nat_lit 3743748224) (nat_lit 0) D2M8K2.t9659 from rfl, totK_node, tot9658, tot9659]
  decide +kernel

theorem arows9652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9652 = true := by
  rw [show D2M8K2.u9652 = KTree.node D2M8K2.t9660 (nat_lit 20712396) (nat_lit 3485394648) (nat_lit 0) D2M8K2.t9661 from rfl, allE_node, rows9660, irow9652, rows9661]
  all_goals rfl

theorem atot9652 : totK PD2M8K2 D2M8K2.u9652 = [0, 363546564450, 890748849638, 490840852308, 68380991724, 1429815836, 0, 0] := by
  rw [show D2M8K2.u9652 = KTree.node D2M8K2.t9660 (nat_lit 20712396) (nat_lit 3485394648) (nat_lit 0) D2M8K2.t9661 from rfl, totK_node, tot9660, tot9661]
  decide +kernel

theorem arows9653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9653 = true := by
  rw [show D2M8K2.u9653 = KTree.node D2M8K2.t9662 (nat_lit 20713923) (nat_lit 3692386415) (nat_lit 0) D2M8K2.t9663 from rfl, allE_node, rows9662, irow9653, rows9663]
  all_goals rfl

theorem atot9653 : totK PD2M8K2 D2M8K2.u9653 = [0, 63803697449, 540942343774, 891781254240, 275308018482, 8601231365, 0, 0] := by
  rw [show D2M8K2.u9653 = KTree.node D2M8K2.t9662 (nat_lit 20713923) (nat_lit 3692386415) (nat_lit 0) D2M8K2.t9663 from rfl, totK_node, tot9662, tot9663]
  decide +kernel

theorem arows9659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9659 = true := by
  rw [show D2M8K2.u9659 = KTree.node D2M8K2.t9664 (nat_lit 20736588) (nat_lit 3573707026) (nat_lit 0) D2M8K2.t9665 from rfl, allE_node, rows9664, irow9659, rows9665]
  all_goals rfl

theorem atot9659 : totK PD2M8K2 D2M8K2.u9659 = [0, 308815967182, 792596834836, 522123248107, 146083090261, 13329350693, 0, 0] := by
  rw [show D2M8K2.u9659 = KTree.node D2M8K2.t9664 (nat_lit 20736588) (nat_lit 3573707026) (nat_lit 0) D2M8K2.t9665 from rfl, totK_node, tot9664, tot9665]
  decide +kernel

theorem arows9660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9660 = true := by
  rw [show D2M8K2.u9660 = KTree.node D2M8K2.t9666 (nat_lit 20737890) (nat_lit 2614820527) (nat_lit 0) D2M8K2.t9667 from rfl, allE_node, rows9666, irow9660, rows9667]
  all_goals rfl

theorem atot9660 : totK PD2M8K2 D2M8K2.u9660 = [0, 86938149001, 686072149825, 861523784426, 136627936750, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9660 = KTree.node D2M8K2.t9666 (nat_lit 20737890) (nat_lit 2614820527) (nat_lit 0) D2M8K2.t9667 from rfl, totK_node, tot9666, tot9667]
  decide +kernel

theorem arows9662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9662 = true := by
  rw [show D2M8K2.u9662 = KTree.node D2M8K2.t9668 (nat_lit 20740273) (nat_lit 1157220666) (nat_lit 0) D2M8K2.t9669 from rfl, allE_node, rows9668, irow9662, rows9669]
  all_goals rfl

theorem atot9662 : totK PD2M8K2 D2M8K2.u9662 = [0, 388728884373, 918804973691, 491421904894, 45942560286, 0, 0, 0] := by
  rw [show D2M8K2.u9662 = KTree.node D2M8K2.t9668 (nat_lit 20740273) (nat_lit 1157220666) (nat_lit 0) D2M8K2.t9669 from rfl, totK_node, tot9668, tot9669]
  decide +kernel

theorem arows9663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9663 = true := by
  rw [show D2M8K2.u9663 = KTree.node D2M8K2.t9670 (nat_lit 20741813) (nat_lit 2401362874) (nat_lit 0) D2M8K2.t9671 from rfl, allE_node, rows9670, irow9663, rows9671]
  all_goals rfl

theorem atot9663 : totK PD2M8K2 D2M8K2.u9663 = [0, 19382266435, 453623874380, 917633826072, 391744525478, 24691320395, 0, 0] := by
  rw [show D2M8K2.u9663 = KTree.node D2M8K2.t9670 (nat_lit 20741813) (nat_lit 2401362874) (nat_lit 0) D2M8K2.t9671 from rfl, totK_node, tot9670, tot9671]
  decide +kernel

theorem arows9666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9666 = true := by
  rw [show D2M8K2.u9666 = KTree.node D2M8K2.t9672 (nat_lit 20743246) (nat_lit 3967668050) (nat_lit 0) D2M8K2.t9673 from rfl, allE_node, rows9672, irow9666, rows9673]
  all_goals rfl

theorem atot9666 : totK PD2M8K2 D2M8K2.u9666 = [0, 274925596925, 770442228754, 594072019453, 161999413854, 8073511420, 0, 0] := by
  rw [show D2M8K2.u9666 = KTree.node D2M8K2.t9672 (nat_lit 20743246) (nat_lit 3967668050) (nat_lit 0) D2M8K2.t9673 from rfl, totK_node, tot9672, tot9673]
  decide +kernel

theorem arows9667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9667 = true := by
  rw [show D2M8K2.u9667 = KTree.node D2M8K2.t9674 (nat_lit 20744721) (nat_lit 1455296746) (nat_lit 0) D2M8K2.t9675 from rfl, allE_node, rows9674, irow9667, rows9675]
  all_goals rfl

theorem atot9667 : totK PD2M8K2 D2M8K2.u9667 = [0, 151025757301, 669410349116, 777631558346, 192002786898, 7166294683, 0, 0] := by
  rw [show D2M8K2.u9667 = KTree.node D2M8K2.t9674 (nat_lit 20744721) (nat_lit 1455296746) (nat_lit 0) D2M8K2.t9675 from rfl, totK_node, tot9674, tot9675]
  decide +kernel

theorem arows9669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9669 = true := by
  rw [show D2M8K2.u9669 = KTree.node D2M8K2.t9676 (nat_lit 20753472) (nat_lit 3583556475) (nat_lit 0) D2M8K2.t9677 from rfl, allE_node, rows9676, irow9669, rows9677]
  all_goals rfl

theorem atot9669 : totK PD2M8K2 D2M8K2.u9669 = [0, 261246173568, 773986850630, 629500204752, 134752256294, 4906626486, 0, 0] := by
  rw [show D2M8K2.u9669 = KTree.node D2M8K2.t9676 (nat_lit 20753472) (nat_lit 3583556475) (nat_lit 0) D2M8K2.t9677 from rfl, totK_node, tot9676, tot9677]
  decide +kernel

theorem arows9670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9670 = true := by
  rw [show D2M8K2.u9670 = KTree.node D2M8K2.t9678 (nat_lit 20754956) (nat_lit 900223633) (nat_lit 0) D2M8K2.t9679 from rfl, allE_node, rows9678, irow9670, rows9679]
  all_goals rfl

theorem atot9670 : totK PD2M8K2 D2M8K2.u9670 = [0, 165290289616, 735909306848, 762795831194, 139809572545, 1268739303, 0, 0] := by
  rw [show D2M8K2.u9670 = KTree.node D2M8K2.t9678 (nat_lit 20754956) (nat_lit 900223633) (nat_lit 0) D2M8K2.t9679 from rfl, totK_node, tot9678, tot9679]
  decide +kernel

theorem arows9674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9674 = true := by
  rw [show D2M8K2.u9674 = KTree.node D2M8K2.t9680 (nat_lit 20756656) (nat_lit 3301886704) (nat_lit 0) D2M8K2.t9681 from rfl, allE_node, rows9680, irow9674, rows9681]
  all_goals rfl

theorem atot9674 : totK PD2M8K2 D2M8K2.u9674 = [0, 0, 339286614586, 940175199786, 449679991938, 26130262030, 0, 0] := by
  rw [show D2M8K2.u9674 = KTree.node D2M8K2.t9680 (nat_lit 20756656) (nat_lit 3301886704) (nat_lit 0) D2M8K2.t9681 from rfl, totK_node, tot9680, tot9681]
  decide +kernel

theorem arows9675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9675 = true := by
  rw [show D2M8K2.u9675 = KTree.node D2M8K2.t9682 (nat_lit 20758331) (nat_lit 2858940134) (nat_lit 0) D2M8K2.t9683 from rfl, allE_node, rows9682, irow9675, rows9683]
  all_goals rfl

theorem atot9675 : totK PD2M8K2 D2M8K2.u9675 = [0, 0, 219119061462, 813727424794, 602700730877, 71419803840, 1166720416, 0] := by
  rw [show D2M8K2.u9675 = KTree.node D2M8K2.t9682 (nat_lit 20758331) (nat_lit 2858940134) (nat_lit 0) D2M8K2.t9683 from rfl, totK_node, tot9682, tot9683]
  decide +kernel

theorem arows9677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9677 = true := by
  rw [show D2M8K2.u9677 = KTree.node D2M8K2.t9684 (nat_lit 20760837) (nat_lit 1505766429) (nat_lit 0) D2M8K2.t9685 from rfl, allE_node, rows9684, irow9677, rows9685]
  all_goals rfl

theorem atot9677 : totK PD2M8K2 D2M8K2.u9677 = [0, 0, 405011673002, 942272829918, 460274426184, 25939405395, 0, 0] := by
  rw [show D2M8K2.u9677 = KTree.node D2M8K2.t9684 (nat_lit 20760837) (nat_lit 1505766429) (nat_lit 0) D2M8K2.t9685 from rfl, totK_node, tot9684, tot9685]
  decide +kernel

theorem arows9678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9678 = true := by
  rw [show D2M8K2.u9678 = KTree.node D2M8K2.t9686 (nat_lit 20764210) (nat_lit 4121252693) (nat_lit 0) D2M8K2.t9687 from rfl, allE_node, rows9686, irow9678, rows9687]
  all_goals rfl

theorem atot9678 : totK PD2M8K2 D2M8K2.u9678 = [0, 0, 367364336215, 927778009361, 448855538576, 31016713962, 0, 0] := by
  rw [show D2M8K2.u9678 = KTree.node D2M8K2.t9686 (nat_lit 20764210) (nat_lit 4121252693) (nat_lit 0) D2M8K2.t9687 from rfl, totK_node, tot9686, tot9687]
  decide +kernel

theorem arows9681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9681 = true := by
  rw [show D2M8K2.u9681 = KTree.node D2M8K2.t9688 (nat_lit 20765956) (nat_lit 3866437580) (nat_lit 0) D2M8K2.t9689 from rfl, allE_node, rows9688, irow9681, rows9689]
  all_goals rfl

theorem atot9681 : totK PD2M8K2 D2M8K2.u9681 = [0, 0, 104905721964, 644780621071, 801878204732, 173069093918, 5134755853, 0] := by
  rw [show D2M8K2.u9681 = KTree.node D2M8K2.t9688 (nat_lit 20765956) (nat_lit 3866437580) (nat_lit 0) D2M8K2.t9689 from rfl, totK_node, tot9688, tot9689]
  decide +kernel

theorem arows9682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9682 = true := by
  rw [show D2M8K2.u9682 = KTree.node D2M8K2.t9690 (nat_lit 20774723) (nat_lit 2964435455) (nat_lit 0) D2M8K2.t9691 from rfl, allE_node, rows9690, irow9682, rows9691]
  all_goals rfl

theorem atot9682 : totK PD2M8K2 D2M8K2.u9682 = [0, 0, 368539620913, 960489761767, 441841836367, 22060996162, 0, 0] := by
  rw [show D2M8K2.u9682 = KTree.node D2M8K2.t9690 (nat_lit 20774723) (nat_lit 2964435455) (nat_lit 0) D2M8K2.t9691 from rfl, totK_node, tot9690, tot9691]
  decide +kernel

theorem arows9684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9684 = true := by
  rw [show D2M8K2.u9684 = KTree.node D2M8K2.t9692 (nat_lit 20778362) (nat_lit 4094202298) (nat_lit 0) D2M8K2.t9693 from rfl, allE_node, rows9692, irow9684, rows9693]
  all_goals rfl

theorem atot9684 : totK PD2M8K2 D2M8K2.u9684 = [0, 369999970085, 886030787517, 421729976167, 87907736049, 12306479239, 0, 0] := by
  rw [show D2M8K2.u9684 = KTree.node D2M8K2.t9692 (nat_lit 20778362) (nat_lit 4094202298) (nat_lit 0) D2M8K2.t9693 from rfl, totK_node, tot9692, tot9693]
  decide +kernel

theorem arows9685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9685 = true := by
  rw [show D2M8K2.u9685 = KTree.node D2M8K2.t9694 (nat_lit 20780065) (nat_lit 1561875799) (nat_lit 0) D2M8K2.t9695 from rfl, allE_node, rows9694, irow9685, rows9695]
  all_goals rfl

theorem atot9685 : totK PD2M8K2 D2M8K2.u9685 = [0, 126401146569, 679593879141, 850149425745, 141547092190, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9685 = KTree.node D2M8K2.t9694 (nat_lit 20780065) (nat_lit 1561875799) (nat_lit 0) D2M8K2.t9695 from rfl, totK_node, tot9694, tot9695]
  decide +kernel

theorem arows9690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9690 = true := by
  rw [show D2M8K2.u9690 = KTree.node D2M8K2.t9696 (nat_lit 20781964) (nat_lit 3260575856) (nat_lit 0) D2M8K2.t9697 from rfl, allE_node, rows9696, irow9690, rows9697]
  all_goals rfl

theorem atot9690 : totK PD2M8K2 D2M8K2.u9690 = [0, 326413203195, 933570440191, 531921814276, 42224874995, 0, 0, 0] := by
  rw [show D2M8K2.u9690 = KTree.node D2M8K2.t9696 (nat_lit 20781964) (nat_lit 3260575856) (nat_lit 0) D2M8K2.t9697 from rfl, totK_node, tot9696, tot9697]
  decide +kernel

theorem arows9691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9691 = true := by
  rw [show D2M8K2.u9691 = KTree.node D2M8K2.t9698 (nat_lit 20783527) (nat_lit 2365710545) (nat_lit 0) D2M8K2.t9699 from rfl, allE_node, rows9698, irow9691, rows9699]
  all_goals rfl

theorem atot9691 : totK PD2M8K2 D2M8K2.u9691 = [0, 0, 399693217060, 948075501155, 427676903595, 26026282721, 0, 0] := by
  rw [show D2M8K2.u9691 = KTree.node D2M8K2.t9698 (nat_lit 20783527) (nat_lit 2365710545) (nat_lit 0) D2M8K2.t9699 from rfl, totK_node, tot9698, tot9699]
  decide +kernel

theorem arows9693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9693 = true := by
  rw [show D2M8K2.u9693 = KTree.node D2M8K2.t9700 (nat_lit 20788261) (nat_lit 1152816498) (nat_lit 0) D2M8K2.t9701 from rfl, allE_node, rows9700, irow9693, rows9701]
  all_goals rfl

theorem atot9693 : totK PD2M8K2 D2M8K2.u9693 = [0, 336834876499, 827378571431, 532384122486, 128931636379, 6779302614, 0, 0] := by
  rw [show D2M8K2.u9693 = KTree.node D2M8K2.t9700 (nat_lit 20788261) (nat_lit 1152816498) (nat_lit 0) D2M8K2.t9701 from rfl, totK_node, tot9700, tot9701]
  decide +kernel

theorem arows9694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9694 = true := by
  rw [show D2M8K2.u9694 = KTree.node D2M8K2.t9702 (nat_lit 20789716) (nat_lit 3117413193) (nat_lit 0) D2M8K2.t9703 from rfl, allE_node, rows9702, irow9694, rows9703]
  all_goals rfl

theorem atot9694 : totK PD2M8K2 D2M8K2.u9694 = [0, 100160278937, 640149988336, 827515130083, 219003188956, 9668735432, 0, 0] := by
  rw [show D2M8K2.u9694 = KTree.node D2M8K2.t9702 (nat_lit 20789716) (nat_lit 3117413193) (nat_lit 0) D2M8K2.t9703 from rfl, totK_node, tot9702, tot9703]
  decide +kernel

theorem arows9697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9697 = true := by
  rw [show D2M8K2.u9697 = KTree.node D2M8K2.t9704 (nat_lit 20791560) (nat_lit 3563682590) (nat_lit 0) D2M8K2.t9705 from rfl, allE_node, rows9704, irow9697, rows9705]
  all_goals rfl

theorem atot9697 : totK PD2M8K2 D2M8K2.u9697 = [0, 269355794150, 794228622081, 623766310472, 119306560938, 3521263076, 0, 0] := by
  rw [show D2M8K2.u9697 = KTree.node D2M8K2.t9704 (nat_lit 20791560) (nat_lit 3563682590) (nat_lit 0) D2M8K2.t9705 from rfl, totK_node, tot9704, tot9705]
  decide +kernel

theorem arows9698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9698 = true := by
  rw [show D2M8K2.u9698 = KTree.node D2M8K2.t9706 (nat_lit 20793415) (nat_lit 2334656709) (nat_lit 0) D2M8K2.t9707 from rfl, allE_node, rows9706, irow9698, rows9707]
  all_goals rfl

theorem atot9698 : totK PD2M8K2 D2M8K2.u9698 = [0, 153751864270, 662347577144, 785771754778, 169448689056, 4917684815, 0, 0] := by
  rw [show D2M8K2.u9698 = KTree.node D2M8K2.t9706 (nat_lit 20793415) (nat_lit 2334656709) (nat_lit 0) D2M8K2.t9707 from rfl, totK_node, tot9706, tot9707]
  decide +kernel

theorem arows9700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9700 = true := by
  rw [show D2M8K2.u9700 = KTree.node D2M8K2.t9708 (nat_lit 20795485) (nat_lit 1147796531) (nat_lit 0) D2M8K2.t9709 from rfl, allE_node, rows9708, irow9700, rows9709]
  all_goals rfl

theorem atot9700 : totK PD2M8K2 D2M8K2.u9700 = [0, 342667567071, 943305616107, 512894615024, 37814083716, 0, 0, 0] := by
  rw [show D2M8K2.u9700 = KTree.node D2M8K2.t9708 (nat_lit 20795485) (nat_lit 1147796531) (nat_lit 0) D2M8K2.t9709 from rfl, totK_node, tot9708, tot9709]
  decide +kernel

theorem arows9701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9701 = true := by
  rw [show D2M8K2.u9701 = KTree.node D2M8K2.t9710 (nat_lit 20797121) (nat_lit 2151394428) (nat_lit 0) D2M8K2.t9711 from rfl, allE_node, rows9710, irow9701, rows9711]
  all_goals rfl

theorem atot9701 : totK PD2M8K2 D2M8K2.u9701 = [0, 0, 466605731450, 984194037912, 313997859214, 9869866690, 0, 0] := by
  rw [show D2M8K2.u9701 = KTree.node D2M8K2.t9710 (nat_lit 20797121) (nat_lit 2151394428) (nat_lit 0) D2M8K2.t9711 from rfl, totK_node, tot9710, tot9711]
  decide +kernel

theorem arows9705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9705 = true := by
  rw [show D2M8K2.u9705 = KTree.node D2M8K2.t9712 (nat_lit 20799078) (nat_lit 3866735348) (nat_lit 0) D2M8K2.t9713 from rfl, allE_node, rows9712, irow9705, rows9713]
  all_goals rfl

theorem atot9705 : totK PD2M8K2 D2M8K2.u9705 = [0, 0, 383442995764, 946656019829, 390046855206, 19811798119, 0, 0] := by
  rw [show D2M8K2.u9705 = KTree.node D2M8K2.t9712 (nat_lit 20799078) (nat_lit 3866735348) (nat_lit 0) D2M8K2.t9713 from rfl, totK_node, tot9712, tot9713]
  decide +kernel

theorem arows9706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9706 = true := by
  rw [show D2M8K2.u9706 = KTree.node D2M8K2.t9714 (nat_lit 20800894) (nat_lit 3621418547) (nat_lit 0) D2M8K2.t9715 from rfl, allE_node, rows9714, irow9706, rows9715]
  all_goals rfl

theorem atot9706 : totK PD2M8K2 D2M8K2.u9706 = [0, 0, 110974765372, 753714140228, 785223933521, 94937481643, 1200365979, 0] := by
  rw [show D2M8K2.u9706 = KTree.node D2M8K2.t9714 (nat_lit 20800894) (nat_lit 3621418547) (nat_lit 0) D2M8K2.t9715 from rfl, totK_node, tot9714, tot9715]
  decide +kernel

theorem arows9708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9708 = true := by
  rw [show D2M8K2.u9708 = KTree.node D2M8K2.t9716 (nat_lit 20803182) (nat_lit 4025775211) (nat_lit 0) D2M8K2.t9717 from rfl, allE_node, rows9716, irow9708, rows9717]
  all_goals rfl

theorem atot9708 : totK PD2M8K2 D2M8K2.u9708 = [0, 0, 488453656680, 987641982156, 333732304268, 11930947648, 0, 0] := by
  rw [show D2M8K2.u9708 = KTree.node D2M8K2.t9716 (nat_lit 20803182) (nat_lit 4025775211) (nat_lit 0) D2M8K2.t9717 from rfl, totK_node, tot9716, tot9717]
  decide +kernel

theorem arows9709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9709 = true := by
  rw [show D2M8K2.u9709 = KTree.node D2M8K2.t9718 (nat_lit 20809906) (nat_lit 3136126979) (nat_lit 0) D2M8K2.t9719 from rfl, allE_node, rows9718, irow9709, rows9719]
  all_goals rfl

theorem atot9709 : totK PD2M8K2 D2M8K2.u9709 = [0, 0, 260417273804, 801572934604, 603188743073, 80144941543, 1135526696, 0] := by
  rw [show D2M8K2.u9709 = KTree.node D2M8K2.t9718 (nat_lit 20809906) (nat_lit 3136126979) (nat_lit 0) D2M8K2.t9719 from rfl, totK_node, tot9718, tot9719]
  decide +kernel

theorem arows9712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9712 = true := by
  rw [show D2M8K2.u9712 = KTree.node D2M8K2.t9720 (nat_lit 20811824) (nat_lit 2873176163) (nat_lit 0) D2M8K2.t9721 from rfl, allE_node, rows9720, irow9712, rows9721]
  all_goals rfl

theorem atot9712 : totK PD2M8K2 D2M8K2.u9712 = [0, 0, 267494808591, 775530383954, 593273671713, 118255649246, 4028038878, 0] := by
  rw [show D2M8K2.u9712 = KTree.node D2M8K2.t9720 (nat_lit 20811824) (nat_lit 2873176163) (nat_lit 0) D2M8K2.t9721 from rfl, totK_node, tot9720, tot9721]
  decide +kernel

theorem arows9713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9713 = true := by
  rw [show D2M8K2.u9713 = KTree.node D2M8K2.t9722 (nat_lit 20815874) (nat_lit 4075017946) (nat_lit 0) D2M8K2.t9723 from rfl, allE_node, rows9722, irow9713, rows9723]
  all_goals rfl

theorem atot9713 : totK PD2M8K2 D2M8K2.u9713 = [0, 0, 397480721830, 954514967674, 400480987311, 20244603311, 0, 0] := by
  rw [show D2M8K2.u9713 = KTree.node D2M8K2.t9722 (nat_lit 20815874) (nat_lit 4075017946) (nat_lit 0) D2M8K2.t9723 from rfl, totK_node, tot9722, tot9723]
  decide +kernel

theorem arows9715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9715 = true := by
  rw [show D2M8K2.u9715 = KTree.node D2M8K2.t9724 (nat_lit 20860573) (nat_lit 1369820453) (nat_lit 0) D2M8K2.t9725 from rfl, allE_node, rows9724, irow9715, rows9725]
  all_goals rfl

theorem atot9715 : totK PD2M8K2 D2M8K2.u9715 = [0, 259820415700, 722303040225, 573781511590, 218846348579, 18903156979, 0, 0] := by
  rw [show D2M8K2.u9715 = KTree.node D2M8K2.t9724 (nat_lit 20860573) (nat_lit 1369820453) (nat_lit 0) D2M8K2.t9725 from rfl, totK_node, tot9724, tot9725]
  decide +kernel

theorem arows9716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9716 = true := by
  rw [show D2M8K2.u9716 = KTree.node D2M8K2.t9726 (nat_lit 20862194) (nat_lit 2682837438) (nat_lit 0) D2M8K2.t9727 from rfl, allE_node, rows9726, irow9716, rows9727]
  all_goals rfl

theorem atot9716 : totK PD2M8K2 D2M8K2.u9716 = [0, 153692282375, 721926178452, 767332132960, 120703915658, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9716 = KTree.node D2M8K2.t9726 (nat_lit 20862194) (nat_lit 2682837438) (nat_lit 0) D2M8K2.t9727 from rfl, totK_node, tot9726, tot9727]
  decide +kernel

theorem arows9725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9725 = true := by
  rw [show D2M8K2.u9725 = KTree.node D2M8K2.t9728 (nat_lit 20864494) (nat_lit 3938442003) (nat_lit 0) D2M8K2.t9729 from rfl, allE_node, rows9728, irow9725, rows9729]
  all_goals rfl

theorem atot9725 : totK PD2M8K2 D2M8K2.u9725 = [0, 308494900635, 858505232377, 595952130118, 60265452730, 0, 0, 0] := by
  rw [show D2M8K2.u9725 = KTree.node D2M8K2.t9728 (nat_lit 20864494) (nat_lit 3938442003) (nat_lit 0) D2M8K2.t9729 from rfl, totK_node, tot9728, tot9729]
  decide +kernel

theorem arows9726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9726 = true := by
  rw [show D2M8K2.u9726 = KTree.node D2M8K2.t9730 (nat_lit 20866025) (nat_lit 1503544697) (nat_lit 0) D2M8K2.t9731 from rfl, allE_node, rows9730, irow9726, rows9731]
  all_goals rfl

theorem atot9726 : totK PD2M8K2 D2M8K2.u9726 = [0, 112057722785, 611424246579, 776177489622, 289563549814, 21156369654, 0, 0] := by
  rw [show D2M8K2.u9726 = KTree.node D2M8K2.t9730 (nat_lit 20866025) (nat_lit 1503544697) (nat_lit 0) D2M8K2.t9731 from rfl, totK_node, tot9730, tot9731]
  decide +kernel

theorem arows9728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9728 = true := by
  rw [show D2M8K2.u9728 = KTree.node D2M8K2.t9732 (nat_lit 20867329) (nat_lit 1573088089) (nat_lit 0) D2M8K2.t9733 from rfl, allE_node, rows9732, irow9728, rows9733]
  all_goals rfl

theorem atot9728 : totK PD2M8K2 D2M8K2.u9728 = [0, 187987986912, 605515612549, 726487053895, 262896103244, 9251062635, 0, 0] := by
  rw [show D2M8K2.u9728 = KTree.node D2M8K2.t9732 (nat_lit 20867329) (nat_lit 1573088089) (nat_lit 0) D2M8K2.t9733 from rfl, totK_node, tot9732, tot9733]
  decide +kernel

theorem arows9729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9729 = true := by
  rw [show D2M8K2.u9729 = KTree.node D2M8K2.t9734 (nat_lit 20868902) (nat_lit 4005219356) (nat_lit 0) D2M8K2.t9735 from rfl, allE_node, rows9734, irow9729, rows9735]
  all_goals rfl

theorem atot9729 : totK PD2M8K2 D2M8K2.u9729 = [0, 214328113740, 778598785547, 686086005648, 104237507683, 1164319620, 0, 0] := by
  rw [show D2M8K2.u9729 = KTree.node D2M8K2.t9734 (nat_lit 20868902) (nat_lit 4005219356) (nat_lit 0) D2M8K2.t9735 from rfl, totK_node, tot9734, tot9735]
  decide +kernel

theorem arows9732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9732 = true := by
  rw [show D2M8K2.u9732 = KTree.node D2M8K2.t9736 (nat_lit 20870832) (nat_lit 3582251432) (nat_lit 0) D2M8K2.t9737 from rfl, allE_node, rows9736, irow9732, rows9737]
  all_goals rfl

theorem atot9732 : totK PD2M8K2 D2M8K2.u9732 = [0, 209420353854, 680330412355, 701519217009, 186732513652, 7393276268, 0, 0] := by
  rw [show D2M8K2.u9732 = KTree.node D2M8K2.t9736 (nat_lit 20870832) (nat_lit 3582251432) (nat_lit 0) D2M8K2.t9737 from rfl, totK_node, tot9736, tot9737]
  decide +kernel

theorem arows9733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9733 = true := by
  rw [show D2M8K2.u9733 = KTree.node D2M8K2.t9738 (nat_lit 20872349) (nat_lit 2123910673) (nat_lit 0) D2M8K2.t9739 from rfl, allE_node, rows9738, irow9733, rows9739]
  all_goals rfl

theorem atot9733 : totK PD2M8K2 D2M8K2.u9733 = [0, 212914627170, 788659926179, 687689602753, 108215041724, 1198073392, 0, 0] := by
  rw [show D2M8K2.u9733 = KTree.node D2M8K2.t9738 (nat_lit 20872349) (nat_lit 2123910673) (nat_lit 0) D2M8K2.t9739 from rfl, totK_node, tot9738, tot9739]
  decide +kernel

theorem arows9735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9735 = true := by
  rw [show D2M8K2.u9735 = KTree.node D2M8K2.t9740 (nat_lit 20874074) (nat_lit 4063548690) (nat_lit 0) D2M8K2.t9741 from rfl, allE_node, rows9740, irow9735, rows9741]
  all_goals rfl

theorem atot9735 : totK PD2M8K2 D2M8K2.u9735 = [0, 176984304571, 683729874650, 747245401211, 197050595044, 7458616031, 0, 0] := by
  rw [show D2M8K2.u9735 = KTree.node D2M8K2.t9740 (nat_lit 20874074) (nat_lit 4063548690) (nat_lit 0) D2M8K2.t9741 from rfl, totK_node, tot9740, tot9741]
  decide +kernel

theorem arows9736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9736 = true := by
  rw [show D2M8K2.u9736 = KTree.node D2M8K2.t9742 (nat_lit 20879141) (nat_lit 2300621315) (nat_lit 0) D2M8K2.t9743 from rfl, allE_node, rows9742, irow9736, rows9743]
  all_goals rfl

theorem atot9736 : totK PD2M8K2 D2M8K2.u9736 = [0, 270413446497, 799482257445, 637379971493, 110892720166, 1268739303, 0, 0] := by
  rw [show D2M8K2.u9736 = KTree.node D2M8K2.t9742 (nat_lit 20879141) (nat_lit 2300621315) (nat_lit 0) D2M8K2.t9743 from rfl, totK_node, tot9742, tot9743]
  decide +kernel

theorem arows9740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9740 = true := by
  rw [show D2M8K2.u9740 = KTree.node D2M8K2.t9744 (nat_lit 20880463) (nat_lit 1636405389) (nat_lit 0) D2M8K2.t9745 from rfl, allE_node, rows9744, irow9740, rows9745]
  all_goals rfl

theorem atot9740 : totK PD2M8K2 D2M8K2.u9740 = [0, 0, 428595220328, 956115332096, 379646195942, 22149860293, 0, 0] := by
  rw [show D2M8K2.u9740 = KTree.node D2M8K2.t9744 (nat_lit 20880463) (nat_lit 1636405389) (nat_lit 0) D2M8K2.t9745 from rfl, totK_node, tot9744, tot9745]
  decide +kernel

theorem arows9741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9741 = true := by
  rw [show D2M8K2.u9741 = KTree.node D2M8K2.t9746 (nat_lit 20882304) (nat_lit 3716921436) (nat_lit 0) D2M8K2.t9747 from rfl, allE_node, rows9746, irow9741, rows9747]
  all_goals rfl

theorem atot9741 : totK PD2M8K2 D2M8K2.u9741 = [0, 0, 318874323010, 909429086897, 473311831416, 29434641418, 0, 0] := by
  rw [show D2M8K2.u9741 = KTree.node D2M8K2.t9746 (nat_lit 20882304) (nat_lit 3716921436) (nat_lit 0) D2M8K2.t9747 from rfl, totK_node, tot9746, tot9747]
  decide +kernel

theorem arows9743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9743 = true := by
  rw [show D2M8K2.u9743 = KTree.node D2M8K2.t9748 (nat_lit 20884350) (nat_lit 3676828414) (nat_lit 0) D2M8K2.t9749 from rfl, allE_node, rows9748, irow9743, rows9749]
  all_goals rfl

theorem atot9743 : totK PD2M8K2 D2M8K2.u9743 = [0, 0, 177287502842, 719501835872, 746321982702, 113817337517, 1288491354, 0] := by
  rw [show D2M8K2.u9743 = KTree.node D2M8K2.t9748 (nat_lit 20884350) (nat_lit 3676828414) (nat_lit 0) D2M8K2.t9749 from rfl, totK_node, tot9748, tot9749]
  decide +kernel

theorem arows9744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9744 = true := by
  rw [show D2M8K2.u9744 = KTree.node D2M8K2.t9750 (nat_lit 20886172) (nat_lit 3899941549) (nat_lit 0) D2M8K2.t9751 from rfl, allE_node, rows9750, irow9744, rows9751]
  all_goals rfl

theorem atot9744 : totK PD2M8K2 D2M8K2.u9744 = [0, 0, 410531033598, 970117622416, 391241033333, 23273002249, 0, 0] := by
  rw [show D2M8K2.u9744 = KTree.node D2M8K2.t9750 (nat_lit 20886172) (nat_lit 3899941549) (nat_lit 0) D2M8K2.t9751 from rfl, totK_node, tot9750, tot9751]
  decide +kernel

theorem arows9747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9747 = true := by
  rw [show D2M8K2.u9747 = KTree.node D2M8K2.t9752 (nat_lit 20889538) (nat_lit 4070374803) (nat_lit 0) D2M8K2.t9753 from rfl, allE_node, rows9752, irow9747, rows9753]
  all_goals rfl

theorem atot9747 : totK PD2M8K2 D2M8K2.u9747 = [0, 0, 229231665925, 804078326935, 626849228222, 80680756061, 1054738420, 0] := by
  rw [show D2M8K2.u9747 = KTree.node D2M8K2.t9752 (nat_lit 20889538) (nat_lit 4070374803) (nat_lit 0) D2M8K2.t9753 from rfl, totK_node, tot9752, tot9753]
  decide +kernel

theorem arows9748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9748 = true := by
  rw [show D2M8K2.u9748 = KTree.node D2M8K2.t9754 (nat_lit 20891613) (nat_lit 1089403095) (nat_lit 0) D2M8K2.t9755 from rfl, allE_node, rows9754, irow9748, rows9755]
  all_goals rfl

theorem atot9748 : totK PD2M8K2 D2M8K2.u9748 = [0, 0, 260863396317, 766713510843, 609380241344, 111170893545, 3732315745, 0] := by
  rw [show D2M8K2.u9748 = KTree.node D2M8K2.t9754 (nat_lit 20891613) (nat_lit 1089403095) (nat_lit 0) D2M8K2.t9755 from rfl, totK_node, tot9754, tot9755]
  decide +kernel

theorem arows9750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9750 = true := by
  rw [show D2M8K2.u9750 = KTree.node D2M8K2.t9756 (nat_lit 20893196) (nat_lit 1435973560) (nat_lit 0) D2M8K2.t9757 from rfl, allE_node, rows9756, irow9750, rows9757]
  all_goals rfl

theorem atot9750 : totK PD2M8K2 D2M8K2.u9750 = [0, 0, 155094646364, 732611873363, 718119368469, 120315679453, 2119229067, 0] := by
  rw [show D2M8K2.u9750 = KTree.node D2M8K2.t9756 (nat_lit 20893196) (nat_lit 1435973560) (nat_lit 0) D2M8K2.t9757 from rfl, totK_node, tot9756, tot9757]
  decide +kernel

theorem arows9751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9751 = true := by
  rw [show D2M8K2.u9751 = KTree.node D2M8K2.t9758 (nat_lit 20898772) (nat_lit 4018806574) (nat_lit 0) D2M8K2.t9759 from rfl, allE_node, rows9758, irow9751, rows9759]
  all_goals rfl

theorem atot9751 : totK PD2M8K2 D2M8K2.u9751 = [0, 0, 297532900716, 855797018063, 547558998637, 79910570907, 2719014351, 0] := by
  rw [show D2M8K2.u9751 = KTree.node D2M8K2.t9758 (nat_lit 20898772) (nat_lit 4018806574) (nat_lit 0) D2M8K2.t9759 from rfl, totK_node, tot9758, tot9759]
  decide +kernel

theorem arows9756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9756 = true := by
  rw [show D2M8K2.u9756 = KTree.node D2M8K2.t9760 (nat_lit 20900224) (nat_lit 3595594221) (nat_lit 0) D2M8K2.t9761 from rfl, allE_node, rows9760, irow9756, rows9761]
  all_goals rfl

theorem atot9756 : totK PD2M8K2 D2M8K2.u9756 = [0, 0, 144931693375, 668920324446, 773816417578, 176341673681, 4811815119, 0] := by
  rw [show D2M8K2.u9756 = KTree.node D2M8K2.t9760 (nat_lit 20900224) (nat_lit 3595594221) (nat_lit 0) D2M8K2.t9761 from rfl, totK_node, tot9760, tot9761]
  decide +kernel

theorem arows9757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9757 = true := by
  rw [show D2M8K2.u9757 = KTree.node D2M8K2.t9762 (nat_lit 20901906) (nat_lit 3411630878) (nat_lit 0) D2M8K2.t9763 from rfl, allE_node, rows9762, irow9757, rows9763]
  all_goals rfl

theorem atot9757 : totK PD2M8K2 D2M8K2.u9757 = [0, 219040212753, 507845857846, 386143563508, 439459316436, 207635082825, 16939352947, 0] := by
  rw [show D2M8K2.u9757 = KTree.node D2M8K2.t9762 (nat_lit 20901906) (nat_lit 3411630878) (nat_lit 0) D2M8K2.t9763 from rfl, totK_node, tot9762, tot9763]
  decide +kernel

theorem arows9759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9759 = true := by
  rw [show D2M8K2.u9759 = KTree.node D2M8K2.t9764 (nat_lit 20903408) (nat_lit 2851759091) (nat_lit 0) D2M8K2.t9765 from rfl, allE_node, rows9764, irow9759, rows9765]
  all_goals rfl

theorem atot9759 : totK PD2M8K2 D2M8K2.u9759 = [0, 223385884551, 789361042861, 682057729933, 112977354925, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9759 = KTree.node D2M8K2.t9764 (nat_lit 20903408) (nat_lit 2851759091) (nat_lit 0) D2M8K2.t9765 from rfl, totK_node, tot9764, tot9765]
  decide +kernel

theorem arows9760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9760 = true := by
  rw [show D2M8K2.u9760 = KTree.node D2M8K2.t9766 (nat_lit 20908912) (nat_lit 3388048083) (nat_lit 0) D2M8K2.t9767 from rfl, allE_node, rows9766, irow9760, rows9767]
  all_goals rfl

theorem atot9760 : totK PD2M8K2 D2M8K2.u9760 = [0, 230155881691, 824758621522, 689935131876, 70965858241, 0, 0, 0] := by
  rw [show D2M8K2.u9760 = KTree.node D2M8K2.t9766 (nat_lit 20908912) (nat_lit 3388048083) (nat_lit 0) D2M8K2.t9767 from rfl, totK_node, tot9766, tot9767]
  decide +kernel

theorem arows9763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9763 = true := by
  rw [show D2M8K2.u9763 = KTree.node D2M8K2.t9768 (nat_lit 20910517) (nat_lit 1308261810) (nat_lit 0) D2M8K2.t9769 from rfl, allE_node, rows9768, irow9763, rows9769]
  all_goals rfl

theorem atot9763 : totK PD2M8K2 D2M8K2.u9763 = [0, 169604885810, 684075551774, 744848688462, 162316492836, 7166294683, 0, 0] := by
  rw [show D2M8K2.u9763 = KTree.node D2M8K2.t9768 (nat_lit 20910517) (nat_lit 1308261810) (nat_lit 0) D2M8K2.t9769 from rfl, totK_node, tot9768, tot9769]
  decide +kernel

theorem arows9764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9764 = true := by
  rw [show D2M8K2.u9764 = KTree.node D2M8K2.t9770 (nat_lit 20912382) (nat_lit 3864460395) (nat_lit 0) D2M8K2.t9771 from rfl, allE_node, rows9770, irow9764, rows9771]
  all_goals rfl

theorem atot9764 : totK PD2M8K2 D2M8K2.u9764 = [0, 248757789920, 753087966447, 640778327992, 137121333394, 5883432551, 0, 0] := by
  rw [show D2M8K2.u9764 = KTree.node D2M8K2.t9770 (nat_lit 20912382) (nat_lit 3864460395) (nat_lit 0) D2M8K2.t9771 from rfl, totK_node, tot9770, tot9771]
  decide +kernel

theorem arows9766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9766 = true := by
  rw [show D2M8K2.u9766 = KTree.node D2M8K2.t9772 (nat_lit 20913918) (nat_lit 4027043304) (nat_lit 0) D2M8K2.t9773 from rfl, allE_node, rows9772, irow9766, rows9773]
  all_goals rfl

theorem atot9766 : totK PD2M8K2 D2M8K2.u9766 = [0, 172608502819, 740160931494, 759017520428, 130475765268, 1198073392, 0, 0] := by
  rw [show D2M8K2.u9766 = KTree.node D2M8K2.t9772 (nat_lit 20913918) (nat_lit 4027043304) (nat_lit 0) D2M8K2.t9773 from rfl, totK_node, tot9772, tot9773]
  decide +kernel

theorem arows9767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9767 = true := by
  rw [show D2M8K2.u9767 = KTree.node D2M8K2.t9774 (nat_lit 20915765) (nat_lit 2373513152) (nat_lit 0) D2M8K2.t9775 from rfl, allE_node, rows9774, irow9767, rows9775]
  all_goals rfl

theorem atot9767 : totK PD2M8K2 D2M8K2.u9767 = [0, 223530326880, 665214503169, 654447854864, 207852569693, 12052611869, 0, 0] := by
  rw [show D2M8K2.u9767 = KTree.node D2M8K2.t9774 (nat_lit 20915765) (nat_lit 2373513152) (nat_lit 0) D2M8K2.t9775 from rfl, totK_node, tot9774, tot9775]
  decide +kernel

theorem arows9771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9771 = true := by
  rw [show D2M8K2.u9771 = KTree.node D2M8K2.t9776 (nat_lit 20916968) (nat_lit 3950786586) (nat_lit 0) D2M8K2.t9777 from rfl, allE_node, rows9776, irow9771, rows9777]
  all_goals rfl

theorem atot9771 : totK PD2M8K2 D2M8K2.u9771 = [0, 190692184833, 768552460347, 708250986152, 102456192365, 1096505104, 0, 0] := by
  rw [show D2M8K2.u9771 = KTree.node D2M8K2.t9776 (nat_lit 20916968) (nat_lit 3950786586) (nat_lit 0) D2M8K2.t9777 from rfl, totK_node, tot9776, tot9777]
  decide +kernel

theorem arows9772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9772 = true := by
  rw [show D2M8K2.u9772 = KTree.node D2M8K2.t9778 (nat_lit 20919280) (nat_lit 3266527981) (nat_lit 0) D2M8K2.t9779 from rfl, allE_node, rows9778, irow9772, rows9779]
  all_goals rfl

theorem atot9772 : totK PD2M8K2 D2M8K2.u9772 = [0, 239956161078, 756190861343, 662222554932, 131714035155, 3884009855, 0, 0] := by
  rw [show D2M8K2.u9772 = KTree.node D2M8K2.t9778 (nat_lit 20919280) (nat_lit 3266527981) (nat_lit 0) D2M8K2.t9779 from rfl, totK_node, tot9778, tot9779]
  decide +kernel

theorem arows9774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9774 = true := by
  rw [show D2M8K2.u9774 = KTree.node D2M8K2.t9780 (nat_lit 20920802) (nat_lit 3892913274) (nat_lit 0) D2M8K2.t9781 from rfl, allE_node, rows9780, irow9774, rows9781]
  all_goals rfl

theorem atot9774 : totK PD2M8K2 D2M8K2.u9774 = [0, 179285595908, 735889249784, 742286536669, 136300915764, 1268739303, 0, 0] := by
  rw [show D2M8K2.u9774 = KTree.node D2M8K2.t9780 (nat_lit 20920802) (nat_lit 3892913274) (nat_lit 0) D2M8K2.t9781 from rfl, totK_node, tot9780, tot9781]
  decide +kernel

theorem arows9775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9775 = true := by
  rw [show D2M8K2.u9775 = KTree.node D2M8K2.t9782 (nat_lit 20922488) (nat_lit 2266040828) (nat_lit 0) D2M8K2.t9783 from rfl, allE_node, rows9782, irow9775, rows9783]
  all_goals rfl

theorem atot9775 : totK PD2M8K2 D2M8K2.u9775 = [0, 0, 375193874227, 951310347622, 417384620652, 23302424837, 0, 0] := by
  rw [show D2M8K2.u9775 = KTree.node D2M8K2.t9782 (nat_lit 20922488) (nat_lit 2266040828) (nat_lit 0) D2M8K2.t9783 from rfl, totK_node, tot9782, tot9783]
  decide +kernel

theorem arows9778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9778 = true := by
  rw [show D2M8K2.u9778 = KTree.node D2M8K2.t9784 (nat_lit 20923978) (nat_lit 2969783928) (nat_lit 0) D2M8K2.t9785 from rfl, allE_node, rows9784, irow9778, rows9785]
  all_goals rfl

theorem atot9778 : totK PD2M8K2 D2M8K2.u9778 = [0, 0, 262064736554, 812173861250, 579676780286, 96085622015, 1369150432, 0] := by
  rw [show D2M8K2.u9778 = KTree.node D2M8K2.t9784 (nat_lit 20923978) (nat_lit 2969783928) (nat_lit 0) D2M8K2.t9785 from rfl, totK_node, tot9784, tot9785]
  decide +kernel

theorem arows9779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9779 = true := by
  rw [show D2M8K2.u9779 = KTree.node D2M8K2.t9786 (nat_lit 20929537) (nat_lit 1573088089) (nat_lit 0) D2M8K2.t9787 from rfl, allE_node, rows9786, irow9779, rows9787]
  all_goals rfl

theorem atot9779 : totK PD2M8K2 D2M8K2.u9779 = [0, 0, 229468064979, 851183416850, 608797294978, 65229466032, 0, 0] := by
  rw [show D2M8K2.u9779 = KTree.node D2M8K2.t9786 (nat_lit 20929537) (nat_lit 1573088089) (nat_lit 0) D2M8K2.t9787 from rfl, totK_node, tot9786, tot9787]
  decide +kernel

theorem arows9781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9781 = true := by
  rw [show D2M8K2.u9781 = KTree.node D2M8K2.t9788 (nat_lit 20931169) (nat_lit 1438346136) (nat_lit 0) D2M8K2.t9789 from rfl, allE_node, rows9788, irow9781, rows9789]
  all_goals rfl

theorem atot9781 : totK PD2M8K2 D2M8K2.u9781 = [0, 0, 349594581822, 930412862730, 450522410050, 26567572776, 0, 0] := by
  rw [show D2M8K2.u9781 = KTree.node D2M8K2.t9788 (nat_lit 20931169) (nat_lit 1438346136) (nat_lit 0) D2M8K2.t9789 from rfl, totK_node, tot9788, tot9789]
  decide +kernel

theorem arows9782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9782 = true := by
  rw [show D2M8K2.u9782 = KTree.node D2M8K2.t9790 (nat_lit 20934476) (nat_lit 2312485655) (nat_lit 0) D2M8K2.t9791 from rfl, allE_node, rows9790, irow9782, rows9791]
  all_goals rfl

theorem atot9782 : totK PD2M8K2 D2M8K2.u9782 = [0, 0, 385126447553, 942697283017, 428995213436, 22498016149, 0, 0] := by
  rw [show D2M8K2.u9782 = KTree.node D2M8K2.t9790 (nat_lit 20934476) (nat_lit 2312485655) (nat_lit 0) D2M8K2.t9791 from rfl, totK_node, tot9790, tot9791]
  decide +kernel

theorem arows9788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9788 = true := by
  rw [show D2M8K2.u9788 = KTree.node D2M8K2.t9792 (nat_lit 20937528) (nat_lit 3401985670) (nat_lit 0) D2M8K2.t9793 from rfl, allE_node, rows9792, irow9788, rows9793]
  all_goals rfl

theorem atot9788 : totK PD2M8K2 D2M8K2.u9788 = [0, 0, 351824883632, 944277213569, 429699187028, 23530719713, 0, 0] := by
  rw [show D2M8K2.u9788 = KTree.node D2M8K2.t9792 (nat_lit 20937528) (nat_lit 3401985670) (nat_lit 0) D2M8K2.t9793 from rfl, totK_node, tot9792, tot9793]
  decide +kernel

theorem arows9789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9789 = true := by
  rw [show D2M8K2.u9789 = KTree.node D2M8K2.t9794 (nat_lit 20940843) (nat_lit 3561626417) (nat_lit 0) D2M8K2.t9795 from rfl, allE_node, rows9794, irow9789, rows9795]
  all_goals rfl

theorem atot9789 : totK PD2M8K2 D2M8K2.u9789 = [0, 50669764256, 394825063095, 875622714719, 438070941018, 25657072946, 0, 0] := by
  rw [show D2M8K2.u9789 = KTree.node D2M8K2.t9794 (nat_lit 20940843) (nat_lit 3561626417) (nat_lit 0) D2M8K2.t9795 from rfl, totK_node, tot9794, tot9795]
  decide +kernel

theorem arows9791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9791 = true := by
  rw [show D2M8K2.u9791 = KTree.node D2M8K2.t9796 (nat_lit 20985833) (nat_lit 1463934142) (nat_lit 0) D2M8K2.t9797 from rfl, allE_node, rows9796, irow9791, rows9797]
  all_goals rfl

theorem atot9791 : totK PD2M8K2 D2M8K2.u9791 = [0, 366445468431, 951669728585, 446789242228, 23644186796, 0, 0, 0] := by
  rw [show D2M8K2.u9791 = KTree.node D2M8K2.t9796 (nat_lit 20985833) (nat_lit 1463934142) (nat_lit 0) D2M8K2.t9797 from rfl, totK_node, tot9796, tot9797]
  decide +kernel

theorem arows9792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9792 = true := by
  rw [show D2M8K2.u9792 = KTree.node D2M8K2.t9798 (nat_lit 20987529) (nat_lit 1883383647) (nat_lit 0) D2M8K2.t9799 from rfl, allE_node, rows9798, irow9792, rows9799]
  all_goals rfl

theorem atot9792 : totK PD2M8K2 D2M8K2.u9792 = [0, 86934566719, 675161908158, 880865788843, 152326286839, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9792 = KTree.node D2M8K2.t9798 (nat_lit 20987529) (nat_lit 1883383647) (nat_lit 0) D2M8K2.t9799 from rfl, totK_node, tot9798, tot9799]
  decide +kernel

theorem arows9795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9795 = true := by
  rw [show D2M8K2.u9795 = KTree.node D2M8K2.t9800 (nat_lit 20992909) (nat_lit 1382254861) (nat_lit 0) D2M8K2.t9801 from rfl, allE_node, rows9800, irow9795, rows9801]
  all_goals rfl

theorem atot9795 : totK PD2M8K2 D2M8K2.u9795 = [0, 338671383312, 914598869487, 529351921855, 40972971066, 0, 0, 0] := by
  rw [show D2M8K2.u9795 = KTree.node D2M8K2.t9800 (nat_lit 20992909) (nat_lit 1382254861) (nat_lit 0) D2M8K2.t9801 from rfl, totK_node, tot9800, tot9801]
  decide +kernel

theorem arows9796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9796 = true := by
  rw [show D2M8K2.u9796 = KTree.node D2M8K2.t9802 (nat_lit 20994301) (nat_lit 976806065) (nat_lit 0) D2M8K2.t9803 from rfl, allE_node, rows9802, irow9796, rows9803]
  all_goals rfl

theorem atot9796 : totK PD2M8K2 D2M8K2.u9796 = [0, 84862533686, 515348799866, 879159259852, 281421894821, 13049727234, 0, 0] := by
  rw [show D2M8K2.u9796 = KTree.node D2M8K2.t9802 (nat_lit 20994301) (nat_lit 976806065) (nat_lit 0) D2M8K2.t9803 from rfl, totK_node, tot9802, tot9803]
  decide +kernel

theorem arows9798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9798 = true := by
  rw [show D2M8K2.u9798 = KTree.node D2M8K2.t9804 (nat_lit 20999476) (nat_lit 3822117226) (nat_lit 0) D2M8K2.t9805 from rfl, allE_node, rows9804, irow9798, rows9805]
  all_goals rfl

theorem atot9798 : totK PD2M8K2 D2M8K2.u9798 = [0, 313184947225, 913802607276, 529386621573, 35118656106, 0, 0, 0] := by
  rw [show D2M8K2.u9798 = KTree.node D2M8K2.t9804 (nat_lit 20999476) (nat_lit 3822117226) (nat_lit 0) D2M8K2.t9805 from rfl, totK_node, tot9804, tot9805]
  decide +kernel

theorem arows9799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9799 = true := by
  rw [show D2M8K2.u9799 = KTree.node D2M8K2.t9806 (nat_lit 21001541) (nat_lit 2280755039) (nat_lit 0) D2M8K2.t9807 from rfl, allE_node, rows9806, irow9799, rows9807]
  all_goals rfl

theorem atot9799 : totK PD2M8K2 D2M8K2.u9799 = [0, 128824206414, 639644093582, 828411307349, 179135427579, 4980514959, 0, 0] := by
  rw [show D2M8K2.u9799 = KTree.node D2M8K2.t9806 (nat_lit 21001541) (nat_lit 2280755039) (nat_lit 0) D2M8K2.t9807 from rfl, totK_node, tot9806, tot9807]
  decide +kernel

theorem arows9803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9803 = true := by
  rw [show D2M8K2.u9803 = KTree.node D2M8K2.t9808 (nat_lit 21003121) (nat_lit 1521438384) (nat_lit 0) D2M8K2.t9809 from rfl, allE_node, rows9808, irow9803, rows9809]
  all_goals rfl

theorem atot9803 : totK PD2M8K2 D2M8K2.u9803 = [0, 274734738259, 841016448203, 622737022668, 83275124324, 1268739303, 0, 0] := by
  rw [show D2M8K2.u9803 = KTree.node D2M8K2.t9808 (nat_lit 21003121) (nat_lit 1521438384) (nat_lit 0) D2M8K2.t9809 from rfl, totK_node, tot9808, tot9809]
  decide +kernel

theorem arows9804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9804 = true := by
  rw [show D2M8K2.u9804 = KTree.node D2M8K2.t9810 (nat_lit 21005290) (nat_lit 4015847179) (nat_lit 0) D2M8K2.t9811 from rfl, allE_node, rows9810, irow9804, rows9811]
  all_goals rfl

theorem atot9804 : totK PD2M8K2 D2M8K2.u9804 = [0, 0, 439628554115, 996668231695, 347915769137, 14050534514, 0, 0] := by
  rw [show D2M8K2.u9804 = KTree.node D2M8K2.t9810 (nat_lit 21005290) (nat_lit 4015847179) (nat_lit 0) D2M8K2.t9811 from rfl, totK_node, tot9810, tot9811]
  decide +kernel

theorem arows9806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9806 = true := by
  rw [show D2M8K2.u9806 = KTree.node D2M8K2.t9812 (nat_lit 21006830) (nat_lit 3526561225) (nat_lit 0) D2M8K2.t9813 from rfl, allE_node, rows9812, irow9806, rows9813]
  all_goals rfl

theorem atot9806 : totK PD2M8K2 D2M8K2.u9806 = [0, 0, 295639281079, 870233222928, 508359558737, 55972022509, 1206465782, 0] := by
  rw [show D2M8K2.u9806 = KTree.node D2M8K2.t9812 (nat_lit 21006830) (nat_lit 3526561225) (nat_lit 0) D2M8K2.t9813 from rfl, totK_node, tot9812, tot9813]
  decide +kernel

theorem arows9807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9807 = true := by
  rw [show D2M8K2.u9807 = KTree.node D2M8K2.t9814 (nat_lit 21012528) (nat_lit 3618816864) (nat_lit 0) D2M8K2.t9815 from rfl, allE_node, rows9814, irow9807, rows9815]
  all_goals rfl

theorem atot9807 : totK PD2M8K2 D2M8K2.u9807 = [0, 0, 240846433072, 839657217911, 620281903501, 61966522120, 0, 0] := by
  rw [show D2M8K2.u9807 = KTree.node D2M8K2.t9814 (nat_lit 21012528) (nat_lit 3618816864) (nat_lit 0) D2M8K2.t9815 from rfl, totK_node, tot9814, tot9815]
  decide +kernel

theorem arows9810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9810 = true := by
  rw [show D2M8K2.u9810 = KTree.node D2M8K2.t9816 (nat_lit 21014068) (nat_lit 3758356247) (nat_lit 0) D2M8K2.t9817 from rfl, allE_node, rows9816, irow9810, rows9817]
  all_goals rfl

theorem atot9810 : totK PD2M8K2 D2M8K2.u9810 = [0, 0, 345396852481, 943898176715, 453356635482, 23721092872, 0, 0] := by
  rw [show D2M8K2.u9810 = KTree.node D2M8K2.t9816 (nat_lit 21014068) (nat_lit 3758356247) (nat_lit 0) D2M8K2.t9817 from rfl, totK_node, tot9816, tot9817]
  decide +kernel

theorem arows9811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9811 = true := by
  rw [show D2M8K2.u9811 = KTree.node D2M8K2.t9818 (nat_lit 21020619) (nat_lit 3407093671) (nat_lit 0) D2M8K2.t9819 from rfl, allE_node, rows9818, irow9811, rows9819]
  all_goals rfl

theorem atot9811 : totK PD2M8K2 D2M8K2.u9811 = [0, 0, 384727528558, 970670162814, 400595725086, 17305857240, 0, 0] := by
  rw [show D2M8K2.u9811 = KTree.node D2M8K2.t9818 (nat_lit 21020619) (nat_lit 3407093671) (nat_lit 0) D2M8K2.t9819 from rfl, totK_node, tot9818, tot9819]
  decide +kernel

theorem arows9813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9813 = true := by
  rw [show D2M8K2.u9813 = KTree.node D2M8K2.t9820 (nat_lit 21024315) (nat_lit 3755335418) (nat_lit 0) D2M8K2.t9821 from rfl, allE_node, rows9820, irow9813, rows9821]
  all_goals rfl

theorem atot9813 : totK PD2M8K2 D2M8K2.u9813 = [0, 122380221654, 512117379006, 750668678639, 392629462164, 28866432750, 0, 0] := by
  rw [show D2M8K2.u9813 = KTree.node D2M8K2.t9820 (nat_lit 21024315) (nat_lit 3755335418) (nat_lit 0) D2M8K2.t9821 from rfl, totK_node, tot9820, tot9821]
  decide +kernel

theorem arows9814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9814 = true := by
  rw [show D2M8K2.u9814 = KTree.node D2M8K2.t9822 (nat_lit 21027539) (nat_lit 2246270139) (nat_lit 0) D2M8K2.t9823 from rfl, allE_node, rows9822, irow9814, rows9823]
  all_goals rfl

theorem atot9814 : totK PD2M8K2 D2M8K2.u9814 = [0, 295251761517, 884848947625, 558806993612, 48362515431, 0, 0, 0] := by
  rw [show D2M8K2.u9814 = KTree.node D2M8K2.t9822 (nat_lit 21027539) (nat_lit 2246270139) (nat_lit 0) D2M8K2.t9823 from rfl, totK_node, tot9822, tot9823]
  decide +kernel

theorem arows9819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9819 = true := by
  rw [show D2M8K2.u9819 = KTree.node D2M8K2.t9824 (nat_lit 21029500) (nat_lit 3063654863) (nat_lit 0) D2M8K2.t9825 from rfl, allE_node, rows9824, irow9819, rows9825]
  all_goals rfl

theorem atot9819 : totK PD2M8K2 D2M8K2.u9819 = [0, 179645629122, 709201842966, 807293149998, 145629320373, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9819 = KTree.node D2M8K2.t9824 (nat_lit 21029500) (nat_lit 3063654863) (nat_lit 0) D2M8K2.t9825 from rfl, totK_node, tot9824, tot9825]
  decide +kernel

theorem arows9820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9820 = true := by
  rw [show D2M8K2.u9820 = KTree.node D2M8K2.t9826 (nat_lit 21031394) (nat_lit 3937566641) (nat_lit 0) D2M8K2.t9827 from rfl, allE_node, rows9826, irow9820, rows9827]
  all_goals rfl

theorem atot9820 : totK PD2M8K2 D2M8K2.u9820 = [0, 167807221222, 701992962797, 724462844028, 219389663907, 19138396551, 0, 0] := by
  rw [show D2M8K2.u9820 = KTree.node D2M8K2.t9826 (nat_lit 21031394) (nat_lit 3937566641) (nat_lit 0) D2M8K2.t9827 from rfl, totK_node, tot9826, tot9827]
  decide +kernel

theorem arows9822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9822 = true := by
  rw [show D2M8K2.u9822 = KTree.node D2M8K2.t9828 (nat_lit 21033215) (nat_lit 2174602308) (nat_lit 0) D2M8K2.t9829 from rfl, allE_node, rows9828, irow9822, rows9829]
  all_goals rfl

theorem atot9822 : totK PD2M8K2 D2M8K2.u9822 = [0, 190297476963, 637382666782, 716025678068, 267301742830, 10795899029, 0, 0] := by
  rw [show D2M8K2.u9822 = KTree.node D2M8K2.t9828 (nat_lit 21033215) (nat_lit 2174602308) (nat_lit 0) D2M8K2.t9829 from rfl, totK_node, tot9828, tot9829]
  decide +kernel

theorem arows9823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9823 = true := by
  rw [show D2M8K2.u9823 = KTree.node D2M8K2.t9830 (nat_lit 21038153) (nat_lit 1418625577) (nat_lit 0) D2M8K2.t9831 from rfl, allE_node, rows9830, irow9823, rows9831]
  all_goals rfl

theorem atot9823 : totK PD2M8K2 D2M8K2.u9823 = [0, 246489523295, 805513089760, 658611254397, 105155424107, 1198073392, 0, 0] := by
  rw [show D2M8K2.u9823 = KTree.node D2M8K2.t9830 (nat_lit 21038153) (nat_lit 1418625577) (nat_lit 0) D2M8K2.t9831 from rfl, totK_node, tot9830, tot9831]
  decide +kernel

theorem arows9826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9826 = true := by
  rw [show D2M8K2.u9826 = KTree.node D2M8K2.t9832 (nat_lit 21039804) (nat_lit 2693832383) (nat_lit 0) D2M8K2.t9833 from rfl, allE_node, rows9832, irow9826, rows9833]
  all_goals rfl

theorem atot9826 : totK PD2M8K2 D2M8K2.u9826 = [0, 164892027188, 647010124891, 747607344568, 224363689521, 12052611869, 0, 0] := by
  rw [show D2M8K2.u9826 = KTree.node D2M8K2.t9832 (nat_lit 21039804) (nat_lit 2693832383) (nat_lit 0) D2M8K2.t9833 from rfl, totK_node, tot9832, tot9833]
  decide +kernel

theorem arows9827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9827 = true := by
  rw [show D2M8K2.u9827 = KTree.node D2M8K2.t9834 (nat_lit 21041227) (nat_lit 2224470779) (nat_lit 0) D2M8K2.t9835 from rfl, allE_node, rows9834, irow9827, rows9835]
  all_goals rfl

theorem atot9827 : totK PD2M8K2 D2M8K2.u9827 = [0, 244896690613, 785896664603, 648146840461, 95686423556, 1096505104, 0, 0] := by
  rw [show D2M8K2.u9827 = KTree.node D2M8K2.t9834 (nat_lit 21041227) (nat_lit 2224470779) (nat_lit 0) D2M8K2.t9835 from rfl, totK_node, tot9834, tot9835]
  decide +kernel

theorem arows9829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9829 = true := by
  rw [show D2M8K2.u9829 = KTree.node D2M8K2.t9836 (nat_lit 21043182) (nat_lit 3521303846) (nat_lit 0) D2M8K2.t9837 from rfl, allE_node, rows9836, irow9829, rows9837]
  all_goals rfl

theorem atot9829 : totK PD2M8K2 D2M8K2.u9829 = [0, 166903323934, 716536788827, 775016202663, 153223631877, 3884009855, 0, 0] := by
  rw [show D2M8K2.u9829 = KTree.node D2M8K2.t9836 (nat_lit 21043182) (nat_lit 3521303846) (nat_lit 0) D2M8K2.t9837 from rfl, totK_node, tot9836, tot9837]
  decide +kernel

theorem arows9830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9830 = true := by
  rw [show D2M8K2.u9830 = KTree.node D2M8K2.t9838 (nat_lit 21045066) (nat_lit 3835629738) (nat_lit 0) D2M8K2.t9839 from rfl, allE_node, rows9838, irow9830, rows9839]
  all_goals rfl

theorem atot9830 : totK PD2M8K2 D2M8K2.u9830 = [0, 248200553126, 790265714449, 657980019878, 112088828352, 1268739303, 0, 0] := by
  rw [show D2M8K2.u9830 = KTree.node D2M8K2.t9838 (nat_lit 21045066) (nat_lit 3835629738) (nat_lit 0) D2M8K2.t9839 from rfl, totK_node, tot9838, tot9839]
  decide +kernel

theorem arows9834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9834 = true := by
  rw [show D2M8K2.u9834 = KTree.node D2M8K2.t9840 (nat_lit 21046798) (nat_lit 4009919491) (nat_lit 0) D2M8K2.t9841 from rfl, allE_node, rows9840, irow9834, rows9841]
  all_goals rfl

theorem atot9834 : totK PD2M8K2 D2M8K2.u9834 = [0, 0, 419257487522, 973137693549, 377056443634, 17667404855, 0, 0] := by
  rw [show D2M8K2.u9834 = KTree.node D2M8K2.t9840 (nat_lit 21046798) (nat_lit 4009919491) (nat_lit 0) D2M8K2.t9841 from rfl, totK_node, tot9840, tot9841]
  decide +kernel

theorem arows9835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9835 = true := by
  rw [show D2M8K2.u9835 = KTree.node D2M8K2.t9842 (nat_lit 21048347) (nat_lit 1235489335) (nat_lit 0) D2M8K2.t9843 from rfl, allE_node, rows9842, irow9835, rows9843]
  all_goals rfl

theorem atot9835 : totK PD2M8K2 D2M8K2.u9835 = [0, 0, 277029184295, 858541616688, 550926224967, 66108080676, 1239866073, 0] := by
  rw [show D2M8K2.u9835 = KTree.node D2M8K2.t9842 (nat_lit 21048347) (nat_lit 1235489335) (nat_lit 0) D2M8K2.t9843 from rfl, totK_node, tot9842, tot9843]
  decide +kernel

theorem arows9837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9837 = true := by
  rw [show D2M8K2.u9837 = KTree.node D2M8K2.t9844 (nat_lit 21050825) (nat_lit 1772331530) (nat_lit 0) D2M8K2.t9845 from rfl, allE_node, rows9844, irow9837, rows9845]
  all_goals rfl

theorem atot9837 : totK PD2M8K2 D2M8K2.u9837 = [0, 0, 192564984272, 786461806014, 742837500880, 84009295303, 0, 0] := by
  rw [show D2M8K2.u9837 = KTree.node D2M8K2.t9844 (nat_lit 21050825) (nat_lit 1772331530) (nat_lit 0) D2M8K2.t9845 from rfl, totK_node, tot9844, tot9845]
  decide +kernel

theorem arows9838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9838 = true := by
  rw [show D2M8K2.u9838 = KTree.node D2M8K2.t9846 (nat_lit 21057491) (nat_lit 2843121356) (nat_lit 0) D2M8K2.t9847 from rfl, allE_node, rows9846, irow9838, rows9847]
  all_goals rfl

theorem atot9838 : totK PD2M8K2 D2M8K2.u9838 = [0, 0, 391848858143, 952389884946, 457698079379, 30469635080, 0, 0] := by
  rw [show D2M8K2.u9838 = KTree.node D2M8K2.t9846 (nat_lit 21057491) (nat_lit 2843121356) (nat_lit 0) D2M8K2.t9847 from rfl, totK_node, tot9846, tot9847]
  decide +kernel

theorem arows9841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9841 = true := by
  rw [show D2M8K2.u9841 = KTree.node D2M8K2.t9848 (nat_lit 21058974) (nat_lit 3937483510) (nat_lit 0) D2M8K2.t9849 from rfl, allE_node, rows9848, irow9841, rows9849]
  all_goals rfl

theorem atot9841 : totK PD2M8K2 D2M8K2.u9841 = [0, 0, 200750895001, 789096881848, 685268162904, 101639722378, 1171084559, 0] := by
  rw [show D2M8K2.u9841 = KTree.node D2M8K2.t9848 (nat_lit 21058974) (nat_lit 3937483510) (nat_lit 0) D2M8K2.t9849 from rfl, totK_node, tot9848, tot9849]
  decide +kernel

theorem arows9842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9842 = true := by
  rw [show D2M8K2.u9842 = KTree.node D2M8K2.t9850 (nat_lit 21060659) (nat_lit 2884073042) (nat_lit 0) D2M8K2.t9851 from rfl, allE_node, rows9850, irow9842, rows9851]
  all_goals rfl

theorem atot9842 : totK PD2M8K2 D2M8K2.u9842 = [0, 0, 180533609873, 660681719191, 695005237781, 206865814927, 11934365838, 0] := by
  rw [show D2M8K2.u9842 = KTree.node D2M8K2.t9850 (nat_lit 21060659) (nat_lit 2884073042) (nat_lit 0) D2M8K2.t9851 from rfl, totK_node, tot9850, tot9851]
  decide +kernel

theorem arows9844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9844 = true := by
  rw [show D2M8K2.u9844 = KTree.node D2M8K2.t9852 (nat_lit 21062099) (nat_lit 2115153579) (nat_lit 0) D2M8K2.t9853 from rfl, allE_node, rows9852, irow9844, rows9853]
  all_goals rfl

theorem atot9844 : totK PD2M8K2 D2M8K2.u9844 = [0, 0, 227389655565, 821008499473, 614453238199, 73146911483, 1053411165, 0] := by
  rw [show D2M8K2.u9844 = KTree.node D2M8K2.t9852 (nat_lit 21062099) (nat_lit 2115153579) (nat_lit 0) D2M8K2.t9853 from rfl, totK_node, tot9852, tot9853]
  decide +kernel

theorem arows9845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9845 = true := by
  rw [show D2M8K2.u9845 = KTree.node D2M8K2.t9854 (nat_lit 21064471) (nat_lit 2216876564) (nat_lit 0) D2M8K2.t9855 from rfl, allE_node, rows9854, irow9845, rows9855]
  all_goals rfl

theorem atot9845 : totK PD2M8K2 D2M8K2.u9845 = [0, 0, 239298446566, 773522553033, 636951169988, 108572048346, 3667207281, 0] := by
  rw [show D2M8K2.u9845 = KTree.node D2M8K2.t9854 (nat_lit 21064471) (nat_lit 2216876564) (nat_lit 0) D2M8K2.t9855 from rfl, totK_node, tot9854, tot9855]
  decide +kernel

theorem arows9852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9852 = true := by
  rw [show D2M8K2.u9852 = KTree.node D2M8K2.t9856 (nat_lit 21067780) (nat_lit 3793132651) (nat_lit 0) D2M8K2.t9857 from rfl, allE_node, rows9856, irow9852, rows9857]
  all_goals rfl

theorem atot9852 : totK PD2M8K2 D2M8K2.u9852 = [0, 206444213209, 649620927240, 658876142269, 270135435870, 20249401196, 0, 0] := by
  rw [show D2M8K2.u9852 = KTree.node D2M8K2.t9856 (nat_lit 21067780) (nat_lit 3793132651) (nat_lit 0) D2M8K2.t9857 from rfl, totK_node, tot9856, tot9857]
  decide +kernel

theorem arows9853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9853 = true := by
  rw [show D2M8K2.u9853 = KTree.node D2M8K2.t9858 (nat_lit 21069300) (nat_lit 3215387251) (nat_lit 0) D2M8K2.t9859 from rfl, allE_node, rows9858, irow9853, rows9859]
  all_goals rfl

theorem atot9853 : totK PD2M8K2 D2M8K2.u9853 = [0, 212354357814, 758847955473, 681975579748, 118005409944, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9853 = KTree.node D2M8K2.t9858 (nat_lit 21069300) (nat_lit 3215387251) (nat_lit 0) D2M8K2.t9859 from rfl, totK_node, tot9858, tot9859]
  decide +kernel

theorem arows9855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9855 = true := by
  rw [show D2M8K2.u9855 = KTree.node D2M8K2.t9860 (nat_lit 21071693) (nat_lit 2203909609) (nat_lit 0) D2M8K2.t9861 from rfl, allE_node, rows9860, irow9855, rows9861]
  all_goals rfl

theorem atot9855 : totK PD2M8K2 D2M8K2.u9855 = [0, 241659868299, 843536562769, 685179493817, 67512998204, 0, 0, 0] := by
  rw [show D2M8K2.u9855 = KTree.node D2M8K2.t9860 (nat_lit 21071693) (nat_lit 2203909609) (nat_lit 0) D2M8K2.t9861 from rfl, totK_node, tot9860, tot9861]
  decide +kernel

theorem arows9856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9856 = true := by
  rw [show D2M8K2.u9856 = KTree.node D2M8K2.t9862 (nat_lit 21073549) (nat_lit 1175108356) (nat_lit 0) D2M8K2.t9863 from rfl, allE_node, rows9862, irow9856, rows9863]
  all_goals rfl

theorem atot9856 : totK PD2M8K2 D2M8K2.u9856 = [0, 87996589950, 567372828282, 841247939092, 313358664485, 15110531864, 0, 0] := by
  rw [show D2M8K2.u9856 = KTree.node D2M8K2.t9862 (nat_lit 21073549) (nat_lit 1175108356) (nat_lit 0) D2M8K2.t9863 from rfl, totK_node, tot9862, tot9863]
  decide +kernel

theorem arows9859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9859 = true := by
  rw [show D2M8K2.u9859 = KTree.node D2M8K2.t9864 (nat_lit 21075264) (nat_lit 3705351137) (nat_lit 0) D2M8K2.t9865 from rfl, allE_node, rows9864, irow9859, rows9865]
  all_goals rfl

theorem atot9859 : totK PD2M8K2 D2M8K2.u9859 = [0, 343758631306, 849569166294, 512761006358, 86245175814, 1409560813, 0, 0] := by
  rw [show D2M8K2.u9859 = KTree.node D2M8K2.t9864 (nat_lit 21075264) (nat_lit 3705351137) (nat_lit 0) D2M8K2.t9865 from rfl, totK_node, tot9864, tot9865]
  decide +kernel

theorem arows9860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9860 = true := by
  rw [show D2M8K2.u9860 = KTree.node D2M8K2.t9866 (nat_lit 21077044) (nat_lit 4076853445) (nat_lit 0) D2M8K2.t9867 from rfl, allE_node, rows9866, irow9860, rows9867]
  all_goals rfl

theorem atot9860 : totK PD2M8K2 D2M8K2.u9860 = [0, 54696703286, 512512157033, 906793083796, 267100889233, 13049727234, 0, 0] := by
  rw [show D2M8K2.u9860 = KTree.node D2M8K2.t9866 (nat_lit 21077044) (nat_lit 4076853445) (nat_lit 0) D2M8K2.t9867 from rfl, totK_node, tot9866, tot9867]
  decide +kernel

theorem arows9862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9862 = true := by
  rw [show D2M8K2.u9862 = KTree.node D2M8K2.t9868 (nat_lit 21079086) (nat_lit 4086215485) (nat_lit 0) D2M8K2.t9869 from rfl, allE_node, rows9868, irow9862, rows9869]
  all_goals rfl

theorem atot9862 : totK PD2M8K2 D2M8K2.u9862 = [0, 384367333893, 939679976459, 466249695467, 32910971721, 0, 0, 0] := by
  rw [show D2M8K2.u9862 = KTree.node D2M8K2.t9868 (nat_lit 21079086) (nat_lit 4086215485) (nat_lit 0) D2M8K2.t9869 from rfl, totK_node, tot9868, tot9869]
  decide +kernel

theorem arows9863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9863 = true := by
  rw [show D2M8K2.u9863 = KTree.node D2M8K2.t9870 (nat_lit 21080781) (nat_lit 1427498473) (nat_lit 0) D2M8K2.t9871 from rfl, allE_node, rows9870, irow9863, rows9871]
  all_goals rfl

theorem atot9863 : totK PD2M8K2 D2M8K2.u9863 = [0, 11284885156, 491889835408, 954063555239, 301184637572, 13250685261, 0, 0] := by
  rw [show D2M8K2.u9863 = KTree.node D2M8K2.t9870 (nat_lit 21080781) (nat_lit 1427498473) (nat_lit 0) D2M8K2.t9871 from rfl, totK_node, tot9870, tot9871]
  decide +kernel

theorem arows9867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9867 = true := by
  rw [show D2M8K2.u9867 = KTree.node D2M8K2.t9872 (nat_lit 21082181) (nat_lit 2337965196) (nat_lit 0) D2M8K2.t9873 from rfl, allE_node, rows9872, irow9867, rows9873]
  all_goals rfl

theorem atot9867 : totK PD2M8K2 D2M8K2.u9867 = [0, 360360583288, 904064317051, 494327054708, 44673529114, 0, 0, 0] := by
  rw [show D2M8K2.u9867 = KTree.node D2M8K2.t9872 (nat_lit 21082181) (nat_lit 2337965196) (nat_lit 0) D2M8K2.t9873 from rfl, totK_node, tot9872, tot9873]
  decide +kernel

theorem arows9868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9868 = true := by
  rw [show D2M8K2.u9868 = KTree.node D2M8K2.t9874 (nat_lit 21083712) (nat_lit 2710629201) (nat_lit 0) D2M8K2.t9875 from rfl, allE_node, rows9874, irow9868, rows9875]
  all_goals rfl

theorem atot9868 : totK PD2M8K2 D2M8K2.u9868 = [0, 74989312342, 641116925489, 905221765060, 178749599476, 2165917952, 0, 0] := by
  rw [show D2M8K2.u9868 = KTree.node D2M8K2.t9874 (nat_lit 21083712) (nat_lit 2710629201) (nat_lit 0) D2M8K2.t9875 from rfl, totK_node, tot9874, tot9875]
  decide +kernel

theorem arows9870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9870 = true := by
  rw [show D2M8K2.u9870 = KTree.node D2M8K2.t9876 (nat_lit 21089382) (nat_lit 3866735348) (nat_lit 0) D2M8K2.t9877 from rfl, allE_node, rows9876, irow9870, rows9877]
  all_goals rfl

theorem atot9870 : totK PD2M8K2 D2M8K2.u9870 = [0, 0, 380897920928, 930167166287, 414998958219, 24976640765, 0, 0] := by
  rw [show D2M8K2.u9870 = KTree.node D2M8K2.t9876 (nat_lit 21089382) (nat_lit 3866735348) (nat_lit 0) D2M8K2.t9877 from rfl, totK_node, tot9876, tot9877]
  decide +kernel

theorem arows9871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9871 = true := by
  rw [show D2M8K2.u9871 = KTree.node D2M8K2.t9878 (nat_lit 21091185) (nat_lit 1836478434) (nat_lit 0) D2M8K2.t9879 from rfl, allE_node, rows9878, irow9871, rows9879]
  all_goals rfl

theorem atot9871 : totK PD2M8K2 D2M8K2.u9871 = [0, 0, 128360842656, 771175150208, 746188647036, 99183036863, 1138244013, 0] := by
  rw [show D2M8K2.u9871 = KTree.node D2M8K2.t9878 (nat_lit 21091185) (nat_lit 1836478434) (nat_lit 0) D2M8K2.t9879 from rfl, totK_node, tot9878, tot9879]
  decide +kernel

theorem arows9874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9874 = true := by
  rw [show D2M8K2.u9874 = KTree.node D2M8K2.t9880 (nat_lit 21093216) (nat_lit 3316708010) (nat_lit 0) D2M8K2.t9881 from rfl, allE_node, rows9880, irow9874, rows9881]
  all_goals rfl

theorem atot9874 : totK PD2M8K2 D2M8K2.u9874 = [0, 0, 392781771054, 993934903783, 397112615929, 15289256948, 0, 0] := by
  rw [show D2M8K2.u9874 = KTree.node D2M8K2.t9880 (nat_lit 21093216) (nat_lit 3316708010) (nat_lit 0) D2M8K2.t9881 from rfl, totK_node, tot9880, tot9881]
  decide +kernel

theorem arows9875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9875 = true := by
  rw [show D2M8K2.u9875 = KTree.node D2M8K2.t9882 (nat_lit 21096915) (nat_lit 3064003345) (nat_lit 0) D2M8K2.t9883 from rfl, allE_node, rows9882, irow9875, rows9883]
  all_goals rfl

theorem atot9875 : totK PD2M8K2 D2M8K2.u9875 = [0, 0, 379550730763, 961925443142, 406706438477, 20279531938, 0, 0] := by
  rw [show D2M8K2.u9875 = KTree.node D2M8K2.t9882 (nat_lit 21096915) (nat_lit 3064003345) (nat_lit 0) D2M8K2.t9883 from rfl, totK_node, tot9882, tot9883]
  decide +kernel

theorem arows9877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9877 = true := by
  rw [show D2M8K2.u9877 = KTree.node D2M8K2.t9884 (nat_lit 21100272) (nat_lit 3372091131) (nat_lit 0) D2M8K2.t9885 from rfl, allE_node, rows9884, irow9877, rows9885]
  all_goals rfl

theorem atot9877 : totK PD2M8K2 D2M8K2.u9877 = [0, 0, 384411566497, 945536648530, 446431076337, 21810364108, 0, 0] := by
  rw [show D2M8K2.u9877 = KTree.node D2M8K2.t9884 (nat_lit 21100272) (nat_lit 3372091131) (nat_lit 0) D2M8K2.t9885 from rfl, totK_node, tot9884, tot9885]
  decide +kernel

theorem arows9878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9878 = true := by
  rw [show D2M8K2.u9878 = KTree.node D2M8K2.t9886 (nat_lit 21103303) (nat_lit 2391364211) (nat_lit 0) D2M8K2.t9887 from rfl, allE_node, rows9886, irow9878, rows9887]
  all_goals rfl

theorem atot9878 : totK PD2M8K2 D2M8K2.u9878 = [0, 0, 292707897728, 893416586273, 526875089232, 44073511828, 0, 0] := by
  rw [show D2M8K2.u9878 = KTree.node D2M8K2.t9886 (nat_lit 21103303) (nat_lit 2391364211) (nat_lit 0) D2M8K2.t9887 from rfl, totK_node, tot9886, tot9887]
  decide +kernel

theorem arows9883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9883 = true := by
  rw [show D2M8K2.u9883 = KTree.node D2M8K2.t9888 (nat_lit 21105298) (nat_lit 2290810967) (nat_lit 0) D2M8K2.t9889 from rfl, allE_node, rows9888, irow9883, rows9889]
  all_goals rfl

theorem atot9883 : totK PD2M8K2 D2M8K2.u9883 = [0, 174456625603, 372444996889, 449242623264, 590620578681, 156743133436, 4977114383, 0] := by
  rw [show D2M8K2.u9883 = KTree.node D2M8K2.t9888 (nat_lit 21105298) (nat_lit 2290810967) (nat_lit 0) D2M8K2.t9889 from rfl, totK_node, tot9888, tot9889]
  decide +kernel

theorem arows9884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9884 = true := by
  rw [show D2M8K2.u9884 = KTree.node D2M8K2.t9890 (nat_lit 21110626) (nat_lit 3098337598) (nat_lit 0) D2M8K2.t9891 from rfl, allE_node, rows9890, irow9884, rows9891]
  all_goals rfl

theorem atot9884 : totK PD2M8K2 D2M8K2.u9884 = [0, 244959653743, 784301676686, 640167081367, 106757185371, 1369150432, 0, 0] := by
  rw [show D2M8K2.u9884 = KTree.node D2M8K2.t9890 (nat_lit 21110626) (nat_lit 3098337598) (nat_lit 0) D2M8K2.t9891 from rfl, totK_node, tot9890, tot9891]
  decide +kernel

theorem arows9886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9886 = true := by
  rw [show D2M8K2.u9886 = KTree.node D2M8K2.t9892 (nat_lit 21113020) (nat_lit 3930389489) (nat_lit 0) D2M8K2.t9893 from rfl, allE_node, rows9892, irow9886, rows9893]
  all_goals rfl

theorem atot9886 : totK PD2M8K2 D2M8K2.u9886 = [0, 191448222714, 788054556128, 768799507630, 92522018813, 0, 0, 0] := by
  rw [show D2M8K2.u9886 = KTree.node D2M8K2.t9892 (nat_lit 21113020) (nat_lit 3930389489) (nat_lit 0) D2M8K2.t9893 from rfl, totK_node, tot9892, tot9893]
  decide +kernel

theorem arows9887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9887 = true := by
  rw [show D2M8K2.u9887 = KTree.node D2M8K2.t9894 (nat_lit 21114794) (nat_lit 4139872233) (nat_lit 0) D2M8K2.t9895 from rfl, allE_node, rows9894, irow9887, rows9895]
  all_goals rfl

theorem atot9887 : totK PD2M8K2 D2M8K2.u9887 = [0, 141435500620, 639662785624, 764274762412, 270728611488, 21401067817, 0, 0] := by
  rw [show D2M8K2.u9887 = KTree.node D2M8K2.t9894 (nat_lit 21114794) (nat_lit 4139872233) (nat_lit 0) D2M8K2.t9895 from rfl, totK_node, tot9894, tot9895]
  decide +kernel

theorem arows9890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9890 = true := by
  rw [show D2M8K2.u9890 = KTree.node D2M8K2.t9896 (nat_lit 21116357) (nat_lit 2343662941) (nat_lit 0) D2M8K2.t9897 from rfl, allE_node, rows9896, irow9890, rows9897]
  all_goals rfl

theorem atot9890 : totK PD2M8K2 D2M8K2.u9890 = [0, 240866880190, 703961188166, 638745651969, 216394679290, 10809146906, 0, 0] := by
  rw [show D2M8K2.u9890 = KTree.node D2M8K2.t9896 (nat_lit 21116357) (nat_lit 2343662941) (nat_lit 0) D2M8K2.t9897 from rfl, totK_node, tot9896, tot9897]
  decide +kernel

theorem arows9891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9891 = true := by
  rw [show D2M8K2.u9891 = KTree.node D2M8K2.t9898 (nat_lit 21118002) (nat_lit 2323816094) (nat_lit 0) D2M8K2.t9899 from rfl, allE_node, rows9898, irow9891, rows9899]
  all_goals rfl

theorem atot9891 : totK PD2M8K2 D2M8K2.u9891 = [0, 140907204893, 650896805728, 799958924321, 189397560465, 5398830306, 0, 0] := by
  rw [show D2M8K2.u9891 = KTree.node D2M8K2.t9898 (nat_lit 21118002) (nat_lit 2323816094) (nat_lit 0) D2M8K2.t9899 from rfl, totK_node, tot9898, tot9899]
  decide +kernel

theorem arows9893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9893 = true := by
  rw [show D2M8K2.u9893 = KTree.node D2M8K2.t9900 (nat_lit 21120080) (nat_lit 3470771641) (nat_lit 0) D2M8K2.t9901 from rfl, allE_node, rows9900, irow9893, rows9901]
  all_goals rfl

theorem atot9893 : totK PD2M8K2 D2M8K2.u9893 = [0, 325889798151, 889799402123, 558510356889, 58097355652, 0, 0, 0] := by
  rw [show D2M8K2.u9893 = KTree.node D2M8K2.t9900 (nat_lit 21120080) (nat_lit 3470771641) (nat_lit 0) D2M8K2.t9901 from rfl, totK_node, tot9900, tot9901]
  decide +kernel

theorem arows9894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9894 = true := by
  rw [show D2M8K2.u9894 = KTree.node D2M8K2.t9902 (nat_lit 21121612) (nat_lit 3112923797) (nat_lit 0) D2M8K2.t9903 from rfl, allE_node, rows9902, irow9894, rows9903]
  all_goals rfl

theorem atot9894 : totK PD2M8K2 D2M8K2.u9894 = [0, 89392755611, 593322187292, 865771871617, 240071741089, 9664716404, 0, 0] := by
  rw [show D2M8K2.u9894 = KTree.node D2M8K2.t9902 (nat_lit 21121612) (nat_lit 3112923797) (nat_lit 0) D2M8K2.t9903 from rfl, totK_node, tot9902, tot9903]
  decide +kernel

theorem arows9898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9898 = true := by
  rw [show D2M8K2.u9898 = KTree.node D2M8K2.t9904 (nat_lit 21126915) (nat_lit 3652688098) (nat_lit 0) D2M8K2.t9905 from rfl, allE_node, rows9904, irow9898, rows9905]
  all_goals rfl

theorem atot9898 : totK PD2M8K2 D2M8K2.u9898 = [0, 324007650773, 842955307127, 557684915867, 98599674211, 2567510802, 0, 0] := by
  rw [show D2M8K2.u9898 = KTree.node D2M8K2.t9904 (nat_lit 21126915) (nat_lit 3652688098) (nat_lit 0) D2M8K2.t9905 from rfl, totK_node, tot9904, tot9905]
  decide +kernel

theorem arows9899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9899 = true := by
  rw [show D2M8K2.u9899 = KTree.node D2M8K2.t9906 (nat_lit 21128359) (nat_lit 2195170110) (nat_lit 0) D2M8K2.t9907 from rfl, allE_node, rows9906, irow9899, rows9907]
  all_goals rfl

theorem atot9899 : totK PD2M8K2 D2M8K2.u9899 = [0, 115702863969, 645682086510, 827762933593, 202083870550, 4967996017, 0, 0] := by
  rw [show D2M8K2.u9899 = KTree.node D2M8K2.t9906 (nat_lit 21128359) (nat_lit 2195170110) (nat_lit 0) D2M8K2.t9907 from rfl, totK_node, tot9906, tot9907]
  decide +kernel

theorem arows9901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9901 = true := by
  rw [show D2M8K2.u9901 = KTree.node D2M8K2.t9908 (nat_lit 21130040) (nat_lit 3560153198) (nat_lit 0) D2M8K2.t9909 from rfl, allE_node, rows9908, irow9901, rows9909]
  all_goals rfl

theorem atot9901 : totK PD2M8K2 D2M8K2.u9901 = [0, 0, 392095353641, 955143618977, 410111740655, 22416853141, 0, 0] := by
  rw [show D2M8K2.u9901 = KTree.node D2M8K2.t9908 (nat_lit 21130040) (nat_lit 3560153198) (nat_lit 0) D2M8K2.t9909 from rfl, totK_node, tot9908, tot9909]
  decide +kernel

theorem arows9902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9902 = true := by
  rw [show D2M8K2.u9902 = KTree.node D2M8K2.t9910 (nat_lit 21131616) (nat_lit 3427134575) (nat_lit 0) D2M8K2.t9911 from rfl, allE_node, rows9910, irow9902, rows9911]
  all_goals rfl

theorem atot9902 : totK PD2M8K2 D2M8K2.u9902 = [0, 0, 186405176036, 773762287578, 690440254859, 96730659556, 1310285577, 0] := by
  rw [show D2M8K2.u9902 = KTree.node D2M8K2.t9910 (nat_lit 21131616) (nat_lit 3427134575) (nat_lit 0) D2M8K2.t9911 from rfl, totK_node, tot9910, tot9911]
  decide +kernel

theorem arows9905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9905 = true := by
  rw [show D2M8K2.u9905 = KTree.node D2M8K2.t9912 (nat_lit 21133986) (nat_lit 3153687486) (nat_lit 0) D2M8K2.t9913 from rfl, allE_node, rows9912, irow9905, rows9913]
  all_goals rfl

theorem atot9905 : totK PD2M8K2 D2M8K2.u9905 = [0, 0, 279924992533, 850954917556, 641820667256, 58945746272, 0, 0] := by
  rw [show D2M8K2.u9905 = KTree.node D2M8K2.t9912 (nat_lit 21133986) (nat_lit 3153687486) (nat_lit 0) D2M8K2.t9913 from rfl, totK_node, tot9912, tot9913]
  decide +kernel

theorem arows9906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9906 = true := by
  rw [show D2M8K2.u9906 = KTree.node D2M8K2.t9914 (nat_lit 21137310) (nat_lit 3500032488) (nat_lit 0) D2M8K2.t9915 from rfl, allE_node, rows9914, irow9906, rows9915]
  all_goals rfl

theorem atot9906 : totK PD2M8K2 D2M8K2.u9906 = [0, 0, 361331749160, 939478901307, 459738014620, 27209016401, 0, 0] := by
  rw [show D2M8K2.u9906 = KTree.node D2M8K2.t9914 (nat_lit 21137310) (nat_lit 3500032488) (nat_lit 0) D2M8K2.t9915 from rfl, totK_node, tot9914, tot9915]
  decide +kernel

theorem arows9908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9908 = true := by
  rw [show D2M8K2.u9908 = KTree.node D2M8K2.t9916 (nat_lit 21140725) (nat_lit 1108180387) (nat_lit 0) D2M8K2.t9917 from rfl, allE_node, rows9916, irow9908, rows9917]
  all_goals rfl

theorem atot9908 : totK PD2M8K2 D2M8K2.u9908 = [0, 0, 377945280065, 936225306616, 480270497963, 33477339317, 0, 0] := by
  rw [show D2M8K2.u9908 = KTree.node D2M8K2.t9916 (nat_lit 21140725) (nat_lit 1108180387) (nat_lit 0) D2M8K2.t9917 from rfl, totK_node, tot9916, tot9917]
  decide +kernel

theorem arows9909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9909 = true := by
  rw [show D2M8K2.u9909 = KTree.node D2M8K2.t9918 (nat_lit 21142234) (nat_lit 3479634365) (nat_lit 0) D2M8K2.t9919 from rfl, allE_node, rows9918, irow9909, rows9919]
  all_goals rfl

theorem atot9909 : totK PD2M8K2 D2M8K2.u9909 = [0, 0, 106826467550, 670359423595, 804106160968, 162553579303, 4931404646, 0] := by
  rw [show D2M8K2.u9909 = KTree.node D2M8K2.t9918 (nat_lit 21142234) (nat_lit 3479634365) (nat_lit 0) D2M8K2.t9919 from rfl, totK_node, tot9918, tot9919]
  decide +kernel

theorem arows9915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9915 = true := by
  rw [show D2M8K2.u9915 = KTree.node D2M8K2.t9920 (nat_lit 21147776) (nat_lit 3140548597) (nat_lit 0) D2M8K2.t9921 from rfl, allE_node, rows9920, irow9915, rows9921]
  all_goals rfl

theorem atot9915 : totK PD2M8K2 D2M8K2.u9915 = [0, 0, 344582534647, 911654388271, 516935875276, 43241617317, 0, 0] := by
  rw [show D2M8K2.u9915 = KTree.node D2M8K2.t9920 (nat_lit 21147776) (nat_lit 3140548597) (nat_lit 0) D2M8K2.t9921 from rfl, totK_node, tot9920, tot9921]
  decide +kernel

theorem arows9916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9916 = true := by
  rw [show D2M8K2.u9916 = KTree.node D2M8K2.t9922 (nat_lit 21149308) (nat_lit 3882621633) (nat_lit 0) D2M8K2.t9923 from rfl, allE_node, rows9922, irow9916, rows9923]
  all_goals rfl

theorem atot9916 : totK PD2M8K2 D2M8K2.u9916 = [0, 0, 93518571537, 653051743138, 848713360692, 185203763448, 4854750737, 0] := by
  rw [show D2M8K2.u9916 = KTree.node D2M8K2.t9922 (nat_lit 21149308) (nat_lit 3882621633) (nat_lit 0) D2M8K2.t9923 from rfl, totK_node, tot9922, tot9923]
  decide +kernel

theorem arows9918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9918 = true := by
  rw [show D2M8K2.u9918 = KTree.node D2M8K2.t9924 (nat_lit 21151429) (nat_lit 1354964743) (nat_lit 0) D2M8K2.t9925 from rfl, allE_node, rows9924, irow9918, rows9925]
  all_goals rfl

theorem atot9918 : totK PD2M8K2 D2M8K2.u9918 = [0, 0, 352647316125, 845021306571, 481004063730, 114122006669, 8997553167, 0] := by
  rw [show D2M8K2.u9918 = KTree.node D2M8K2.t9924 (nat_lit 21151429) (nat_lit 1354964743) (nat_lit 0) D2M8K2.t9925 from rfl, totK_node, tot9924, tot9925]
  decide +kernel

theorem arows9919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9919 = true := by
  rw [show D2M8K2.u9919 = KTree.node D2M8K2.t9926 (nat_lit 21152608) (nat_lit 2748006497) (nat_lit 0) D2M8K2.t9927 from rfl, allE_node, rows9926, irow9919, rows9927]
  all_goals rfl

theorem atot9919 : totK PD2M8K2 D2M8K2.u9919 = [0, 0, 87309021245, 689561632566, 873113410690, 143077356788, 1369150432, 0] := by
  rw [show D2M8K2.u9919 = KTree.node D2M8K2.t9926 (nat_lit 21152608) (nat_lit 2748006497) (nat_lit 0) D2M8K2.t9927 from rfl, totK_node, tot9926, tot9927]
  decide +kernel

theorem arows9922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9922 = true := by
  rw [show D2M8K2.u9922 = KTree.node D2M8K2.t9928 (nat_lit 21158306) (nat_lit 3920798455) (nat_lit 0) D2M8K2.t9929 from rfl, allE_node, rows9928, irow9922, rows9929]
  all_goals rfl

theorem atot9922 : totK PD2M8K2 D2M8K2.u9922 = [0, 0, 387113202088, 918955955257, 444611794469, 26606755026, 0, 0] := by
  rw [show D2M8K2.u9922 = KTree.node D2M8K2.t9928 (nat_lit 21158306) (nat_lit 3920798455) (nat_lit 0) D2M8K2.t9929 from rfl, totK_node, tot9928, tot9929]
  decide +kernel

theorem arows9923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9923 = true := by
  rw [show D2M8K2.u9923 = KTree.node D2M8K2.t9930 (nat_lit 21160057) (nat_lit 1469442310) (nat_lit 0) D2M8K2.t9931 from rfl, allE_node, rows9930, irow9923, rows9931]
  all_goals rfl

theorem atot9923 : totK PD2M8K2 D2M8K2.u9923 = [0, 0, 111445048698, 735974713679, 830349956274, 109954097063, 1164319620, 0] := by
  rw [show D2M8K2.u9923 = KTree.node D2M8K2.t9930 (nat_lit 21160057) (nat_lit 1469442310) (nat_lit 0) D2M8K2.t9931 from rfl, totK_node, tot9930, tot9931]
  decide +kernel

theorem arows9925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9925 = true := by
  rw [show D2M8K2.u9925 = KTree.node D2M8K2.t9932 (nat_lit 21162293) (nat_lit 2316623341) (nat_lit 0) D2M8K2.t9933 from rfl, allE_node, rows9932, irow9925, rows9933]
  all_goals rfl

theorem atot9925 : totK PD2M8K2 D2M8K2.u9925 = [0, 0, 312252601301, 880215131672, 551863016227, 41837648588, 0, 0] := by
  rw [show D2M8K2.u9925 = KTree.node D2M8K2.t9932 (nat_lit 21162293) (nat_lit 2316623341) (nat_lit 0) D2M8K2.t9933 from rfl, totK_node, tot9932, tot9933]
  decide +kernel

theorem arows9926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9926 = true := by
  rw [show D2M8K2.u9926 = KTree.node D2M8K2.t9934 (nat_lit 21163999) (nat_lit 2331222432) (nat_lit 0) D2M8K2.t9935 from rfl, allE_node, rows9934, irow9926, rows9935]
  all_goals rfl

theorem atot9926 : totK PD2M8K2 D2M8K2.u9926 = [0, 0, 87770539582, 534904054446, 856174233433, 253779964973, 13092379805, 0] := by
  rw [show D2M8K2.u9926 = KTree.node D2M8K2.t9934 (nat_lit 21163999) (nat_lit 2331222432) (nat_lit 0) D2M8K2.t9935 from rfl, totK_node, tot9934, tot9935]
  decide +kernel

theorem arows9930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9930 = true := by
  rw [show D2M8K2.u9930 = KTree.node D2M8K2.t9936 (nat_lit 21165442) (nat_lit 2643774154) (nat_lit 0) D2M8K2.t9937 from rfl, allE_node, rows9936, irow9930, rows9937]
  all_goals rfl

theorem atot9930 : totK PD2M8K2 D2M8K2.u9930 = [0, 0, 322612705382, 889392442571, 503513100530, 32776490667, 0, 0] := by
  rw [show D2M8K2.u9930 = KTree.node D2M8K2.t9936 (nat_lit 21165442) (nat_lit 2643774154) (nat_lit 0) D2M8K2.t9937 from rfl, totK_node, tot9936, tot9937]
  decide +kernel

theorem arows9931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9931 = true := by
  rw [show D2M8K2.u9931 = KTree.node D2M8K2.t9938 (nat_lit 21167434) (nat_lit 2518791642) (nat_lit 0) D2M8K2.t9939 from rfl, allE_node, rows9938, irow9931, rows9939]
  all_goals rfl

theorem atot9931 : totK PD2M8K2 D2M8K2.u9931 = [0, 0, 155397482314, 647726982217, 800401803201, 157317631483, 4934531535, 0] := by
  rw [show D2M8K2.u9931 = KTree.node D2M8K2.t9938 (nat_lit 21167434) (nat_lit 2518791642) (nat_lit 0) D2M8K2.t9939 from rfl, totK_node, tot9938, tot9939]
  decide +kernel

theorem arows9933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9933 = true := by
  rw [show D2M8K2.u9933 = KTree.node D2M8K2.t9940 (nat_lit 21169090) (nat_lit 3946866417) (nat_lit 0) D2M8K2.t9941 from rfl, allE_node, rows9940, irow9933, rows9941]
  all_goals rfl

theorem atot9933 : totK PD2M8K2 D2M8K2.u9933 = [0, 0, 259374554225, 823943567410, 621543614415, 84455138619, 1268739303, 0] := by
  rw [show D2M8K2.u9933 = KTree.node D2M8K2.t9940 (nat_lit 21169090) (nat_lit 3946866417) (nat_lit 0) D2M8K2.t9941 from rfl, totK_node, tot9940, tot9941]
  decide +kernel

theorem arows9934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9934 = true := by
  rw [show D2M8K2.u9934 = KTree.node D2M8K2.t9942 (nat_lit 21171227) (nat_lit 2913744014) (nat_lit 0) D2M8K2.t9943 from rfl, allE_node, rows9942, irow9934, rows9943]
  all_goals rfl

theorem atot9934 : totK PD2M8K2 D2M8K2.u9934 = [0, 0, 0, 486947386980, 967875684520, 299745822430, 13954627394, 0] := by
  rw [show D2M8K2.u9934 = KTree.node D2M8K2.t9942 (nat_lit 21171227) (nat_lit 2913744014) (nat_lit 0) D2M8K2.t9943 from rfl, totK_node, tot9942, tot9943]
  decide +kernel

theorem arows9937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9937 = true := by
  rw [show D2M8K2.u9937 = KTree.node D2M8K2.t9944 (nat_lit 21172783) (nat_lit 1701641419) (nat_lit 0) D2M8K2.t9945 from rfl, allE_node, rows9944, irow9937, rows9945]
  all_goals rfl

theorem atot9937 : totK PD2M8K2 D2M8K2.u9937 = [0, 0, 0, 266124542848, 830603563792, 550321886428, 79991691165, 1369150432] := by
  rw [show D2M8K2.u9937 = KTree.node D2M8K2.t9944 (nat_lit 21172783) (nat_lit 1701641419) (nat_lit 0) D2M8K2.t9945 from rfl, totK_node, tot9944, tot9945]
  decide +kernel

theorem arows9938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9938 = true := by
  rw [show D2M8K2.u9938 = KTree.node D2M8K2.t9946 (nat_lit 21178449) (nat_lit 1690629529) (nat_lit 0) D2M8K2.t9947 from rfl, allE_node, rows9946, irow9938, rows9947]
  all_goals rfl

theorem atot9938 : totK PD2M8K2 D2M8K2.u9938 = [0, 0, 0, 274259457055, 897824735739, 517650852285, 41710789937, 0] := by
  rw [show D2M8K2.u9938 = KTree.node D2M8K2.t9946 (nat_lit 21178449) (nat_lit 1690629529) (nat_lit 0) D2M8K2.t9947 from rfl, totK_node, tot9946, tot9947]
  decide +kernel

theorem arows9940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9940 = true := by
  rw [show D2M8K2.u9940 = KTree.node D2M8K2.t9948 (nat_lit 21182209) (nat_lit 1175639595) (nat_lit 0) D2M8K2.t9949 from rfl, allE_node, rows9948, irow9940, rows9949]
  all_goals rfl

theorem atot9940 : totK PD2M8K2 D2M8K2.u9940 = [0, 0, 0, 442497326140, 991519163995, 316817598733, 11937823036, 0] := by
  rw [show D2M8K2.u9940 = KTree.node D2M8K2.t9948 (nat_lit 21182209) (nat_lit 1175639595) (nat_lit 0) D2M8K2.t9949 from rfl, totK_node, tot9948, tot9949]
  decide +kernel

theorem arows9941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9941 = true := by
  rw [show D2M8K2.u9941 = KTree.node D2M8K2.t9950 (nat_lit 21185630) (nat_lit 2072152829) (nat_lit 8) D2M8K2.t9951 from rfl, allE_node, rows9950, irow9941, rows9951]
  all_goals rfl

theorem atot9941 : totK PD2M8K2 D2M8K2.u9941 = [0, 0, 0, 413379665891, 936418759930, 342590543023, 22268810479, 0] := by
  rw [show D2M8K2.u9941 = KTree.node D2M8K2.t9950 (nat_lit 21185630) (nat_lit 2072152829) (nat_lit 8) D2M8K2.t9951 from rfl, totK_node, tot9950, tot9951]
  decide +kernel

theorem arows9946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9946 = true := by
  rw [show D2M8K2.u9946 = KTree.node D2M8K2.t9952 (nat_lit 21189158) (nat_lit 3263128808) (nat_lit 544) D2M8K2.t9953 from rfl, allE_node, rows9952, irow9946, rows9953]
  all_goals rfl

theorem atot9946 : totK PD2M8K2 D2M8K2.u9946 = [0, 0, 0, 481514165952, 993701060832, 302937218297, 10379672289, 0] := by
  rw [show D2M8K2.u9946 = KTree.node D2M8K2.t9952 (nat_lit 21189158) (nat_lit 3263128808) (nat_lit 544) D2M8K2.t9953 from rfl, totK_node, tot9952, tot9953]
  decide +kernel

theorem arows9947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9947 = true := by
  rw [show D2M8K2.u9947 = KTree.node D2M8K2.t9954 (nat_lit 21234454) (nat_lit 2983288571) (nat_lit 0) D2M8K2.t9955 from rfl, allE_node, rows9954, irow9947, rows9955]
  all_goals rfl

theorem atot9947 : totK PD2M8K2 D2M8K2.u9947 = [0, 0, 357382445986, 872362195608, 450952530876, 74423305364, 7717210273, 0] := by
  rw [show D2M8K2.u9947 = KTree.node D2M8K2.t9954 (nat_lit 21234454) (nat_lit 2983288571) (nat_lit 0) D2M8K2.t9955 from rfl, totK_node, tot9954, tot9955]
  decide +kernel

theorem arows9949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9949 = true := by
  rw [show D2M8K2.u9949 = KTree.node D2M8K2.t9956 (nat_lit 21236064) (nat_lit 3516774358) (nat_lit 0) D2M8K2.t9957 from rfl, allE_node, rows9956, irow9949, rows9957]
  all_goals rfl

theorem atot9949 : totK PD2M8K2 D2M8K2.u9949 = [0, 0, 129211462190, 699703828092, 835718932018, 120422246144, 1369150432, 0] := by
  rw [show D2M8K2.u9949 = KTree.node D2M8K2.t9956 (nat_lit 21236064) (nat_lit 3516774358) (nat_lit 0) D2M8K2.t9957 from rfl, totK_node, tot9956, tot9957]
  decide +kernel

theorem arows9950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9950 = true := by
  rw [show D2M8K2.u9950 = KTree.node D2M8K2.t9958 (nat_lit 21241326) (nat_lit 2527521374) (nat_lit 0) D2M8K2.t9959 from rfl, allE_node, rows9958, irow9950, rows9959]
  all_goals rfl

theorem atot9950 : totK PD2M8K2 D2M8K2.u9950 = [0, 0, 352265566925, 943849803429, 486140754940, 26494297946, 0, 0] := by
  rw [show D2M8K2.u9950 = KTree.node D2M8K2.t9958 (nat_lit 21241326) (nat_lit 2527521374) (nat_lit 0) D2M8K2.t9959 from rfl, totK_node, tot9958, tot9959]
  decide +kernel

theorem arows9953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9953 = true := by
  rw [show D2M8K2.u9953 = KTree.node D2M8K2.t9960 (nat_lit 21243486) (nat_lit 2710853690) (nat_lit 0) D2M8K2.t9961 from rfl, allE_node, rows9960, irow9953, rows9961]
  all_goals rfl

theorem atot9953 : totK PD2M8K2 D2M8K2.u9953 = [0, 0, 149090311686, 747116854797, 780675059658, 110706011473, 1164319620, 0] := by
  rw [show D2M8K2.u9953 = KTree.node D2M8K2.t9960 (nat_lit 21243486) (nat_lit 2710853690) (nat_lit 0) D2M8K2.t9961 from rfl, totK_node, tot9960, tot9961]
  decide +kernel

theorem arows9954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9954 = true := by
  rw [show D2M8K2.u9954 = KTree.node D2M8K2.t9962 (nat_lit 21248582) (nat_lit 2508270749) (nat_lit 0) D2M8K2.t9963 from rfl, allE_node, rows9962, irow9954, rows9963]
  all_goals rfl

theorem atot9954 : totK PD2M8K2 D2M8K2.u9954 = [0, 0, 247859140455, 822362996743, 612450269691, 74729750312, 1096505104, 0] := by
  rw [show D2M8K2.u9954 = KTree.node D2M8K2.t9962 (nat_lit 21248582) (nat_lit 2508270749) (nat_lit 0) D2M8K2.t9963 from rfl, totK_node, tot9962, tot9963]
  decide +kernel

theorem arows9956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9956 = true := by
  rw [show D2M8K2.u9956 = KTree.node D2M8K2.t9964 (nat_lit 21251049) (nat_lit 1833435277) (nat_lit 0) D2M8K2.t9965 from rfl, allE_node, rows9964, irow9956, rows9965]
  all_goals rfl

theorem atot9956 : totK PD2M8K2 D2M8K2.u9956 = [0, 0, 242263205799, 837452346868, 676505171647, 55810759200, 0, 0] := by
  rw [show D2M8K2.u9956 = KTree.node D2M8K2.t9964 (nat_lit 21251049) (nat_lit 1833435277) (nat_lit 0) D2M8K2.t9965 from rfl, totK_node, tot9964, tot9965]
  decide +kernel

theorem arows9957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9957 = true := by
  rw [show D2M8K2.u9957 = KTree.node D2M8K2.t9966 (nat_lit 21275233) (nat_lit 1511738784) (nat_lit 0) D2M8K2.t9967 from rfl, allE_node, rows9966, irow9957, rows9967]
  all_goals rfl

theorem atot9957 : totK PD2M8K2 D2M8K2.u9957 = [0, 0, 407094841120, 939973911385, 427162714166, 24997764712, 0, 0] := by
  rw [show D2M8K2.u9957 = KTree.node D2M8K2.t9966 (nat_lit 21275233) (nat_lit 1511738784) (nat_lit 0) D2M8K2.t9967 from rfl, totK_node, tot9966, tot9967]
  decide +kernel

theorem arows9961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9961 = true := by
  rw [show D2M8K2.u9961 = KTree.node D2M8K2.t9968 (nat_lit 21276788) (nat_lit 1659074422) (nat_lit 0) D2M8K2.t9969 from rfl, allE_node, rows9968, irow9961, rows9969]
  all_goals rfl

theorem atot9961 : totK PD2M8K2 D2M8K2.u9961 = [0, 0, 168704404144, 738539834921, 743592172893, 116576617296, 1369150432, 0] := by
  rw [show D2M8K2.u9961 = KTree.node D2M8K2.t9968 (nat_lit 21276788) (nat_lit 1659074422) (nat_lit 0) D2M8K2.t9969 from rfl, totK_node, tot9968, tot9969]
  decide +kernel

theorem arows9962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9962 = true := by
  rw [show D2M8K2.u9962 = KTree.node D2M8K2.t9970 (nat_lit 21279140) (nat_lit 3655163336) (nat_lit 0) D2M8K2.t9971 from rfl, allE_node, rows9970, irow9962, rows9971]
  all_goals rfl

theorem atot9962 : totK PD2M8K2 D2M8K2.u9962 = [0, 0, 275105921235, 843824909445, 645338164738, 64106159850, 0, 0] := by
  rw [show D2M8K2.u9962 = KTree.node D2M8K2.t9970 (nat_lit 21279140) (nat_lit 3655163336) (nat_lit 0) D2M8K2.t9971 from rfl, totK_node, tot9970, tot9971]
  decide +kernel

theorem arows9964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9964 = true := by
  rw [show D2M8K2.u9964 = KTree.node D2M8K2.t9972 (nat_lit 21281401) (nat_lit 1332950728) (nat_lit 0) D2M8K2.t9973 from rfl, allE_node, rows9972, irow9964, rows9973]
  all_goals rfl

theorem atot9964 : totK PD2M8K2 D2M8K2.u9964 = [0, 0, 157141310321, 674802430691, 797757752392, 194873351762, 5348807592, 0] := by
  rw [show D2M8K2.u9964 = KTree.node D2M8K2.t9972 (nat_lit 21281401) (nat_lit 1332950728) (nat_lit 0) D2M8K2.t9973 from rfl, totK_node, tot9972, tot9973]
  decide +kernel

theorem arows9965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9965 = true := by
  rw [show D2M8K2.u9965 = KTree.node D2M8K2.t9974 (nat_lit 21286522) (nat_lit 3806569382) (nat_lit 0) D2M8K2.t9975 from rfl, allE_node, rows9974, irow9965, rows9975]
  all_goals rfl

theorem atot9965 : totK PD2M8K2 D2M8K2.u9965 = [0, 0, 352407060089, 941459732588, 504730841076, 34028414980, 0, 0] := by
  rw [show D2M8K2.u9965 = KTree.node D2M8K2.t9974 (nat_lit 21286522) (nat_lit 3806569382) (nat_lit 0) D2M8K2.t9975 from rfl, totK_node, tot9974, tot9975]
  decide +kernel

theorem arows9968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9968 = true := by
  rw [show D2M8K2.u9968 = KTree.node D2M8K2.t9976 (nat_lit 21288196) (nat_lit 2560164666) (nat_lit 0) D2M8K2.t9977 from rfl, allE_node, rows9976, irow9968, rows9977]
  all_goals rfl

theorem atot9968 : totK PD2M8K2 D2M8K2.u9968 = [0, 0, 0, 485508591832, 988280065250, 294824814984, 13170675918, 0] := by
  rw [show D2M8K2.u9968 = KTree.node D2M8K2.t9976 (nat_lit 21288196) (nat_lit 2560164666) (nat_lit 0) D2M8K2.t9977 from rfl, totK_node, tot9976, tot9977]
  decide +kernel

theorem arows9969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9969 = true := by
  rw [show D2M8K2.u9969 = KTree.node D2M8K2.t9978 (nat_lit 21289569) (nat_lit 1826690268) (nat_lit 0) D2M8K2.t9979 from rfl, allE_node, rows9978, irow9969, rows9979]
  all_goals rfl

theorem atot9969 : totK PD2M8K2 D2M8K2.u9969 = [0, 0, 389229984677, 915710768632, 452583254725, 33381063644, 0, 0] := by
  rw [show D2M8K2.u9969 = KTree.node D2M8K2.t9978 (nat_lit 21289569) (nat_lit 1826690268) (nat_lit 0) D2M8K2.t9979 from rfl, totK_node, tot9978, tot9979]
  decide +kernel

theorem arows9971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9971 = true := by
  rw [show D2M8K2.u9971 = KTree.node D2M8K2.t9980 (nat_lit 21291322) (nat_lit 1648305324) (nat_lit 2048) D2M8K2.t9981 from rfl, allE_node, rows9980, irow9971, rows9981]
  all_goals rfl

theorem atot9971 : totK PD2M8K2 D2M8K2.u9971 = [0, 0, 91822518919, 629081334274, 864841582640, 169027849633, 4917684815, 0] := by
  rw [show D2M8K2.u9971 = KTree.node D2M8K2.t9980 (nat_lit 21291322) (nat_lit 1648305324) (nat_lit 2048) D2M8K2.t9981 from rfl, totK_node, tot9980, tot9981]
  decide +kernel

theorem arows9972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9972 = true := by
  rw [show D2M8K2.u9972 = KTree.node D2M8K2.t9982 (nat_lit 21293287) (nat_lit 2386616747) (nat_lit 0) D2M8K2.t9983 from rfl, allE_node, rows9982, irow9972, rows9983]
  all_goals rfl

theorem atot9972 : totK PD2M8K2 D2M8K2.u9972 = [0, 0, 335839943831, 925922650274, 534943274673, 40228974943, 0, 0] := by
  rw [show D2M8K2.u9972 = KTree.node D2M8K2.t9982 (nat_lit 21293287) (nat_lit 2386616747) (nat_lit 0) D2M8K2.t9983 from rfl, totK_node, tot9982, tot9983]
  decide +kernel

theorem arows9980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9980 = true := by
  rw [show D2M8K2.u9980 = KTree.node D2M8K2.t9984 (nat_lit 21295139) (nat_lit 2964126074) (nat_lit 0) D2M8K2.t9985 from rfl, allE_node, rows9984, irow9980, rows9985]
  all_goals rfl

theorem atot9980 : totK PD2M8K2 D2M8K2.u9980 = [0, 0, 90861460542, 559984121325, 860872393654, 265628613145, 13714665880, 0] := by
  rw [show D2M8K2.u9980 = KTree.node D2M8K2.t9984 (nat_lit 21295139) (nat_lit 2964126074) (nat_lit 0) D2M8K2.t9985 from rfl, totK_node, tot9984, tot9985]
  decide +kernel

theorem arows9981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9981 = true := by
  rw [show D2M8K2.u9981 = KTree.node D2M8K2.t9986 (nat_lit 21317706) (nat_lit 3721400068) (nat_lit 0) D2M8K2.t9987 from rfl, allE_node, rows9986, irow9981, rows9987]
  all_goals rfl

theorem atot9981 : totK PD2M8K2 D2M8K2.u9981 = [0, 0, 323906130289, 907486469089, 483761152763, 31135212540, 0, 0] := by
  rw [show D2M8K2.u9981 = KTree.node D2M8K2.t9986 (nat_lit 21317706) (nat_lit 3721400068) (nat_lit 0) D2M8K2.t9987 from rfl, totK_node, tot9986, tot9987]
  decide +kernel

theorem arows9983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9983 = true := by
  rw [show D2M8K2.u9983 = KTree.node D2M8K2.t9988 (nat_lit 21319533) (nat_lit 1392942350) (nat_lit 0) D2M8K2.t9989 from rfl, allE_node, rows9988, irow9983, rows9989]
  all_goals rfl

theorem atot9983 : totK PD2M8K2 D2M8K2.u9983 = [0, 0, 138449963357, 688823120513, 840274142424, 135799449421, 1369150432, 0] := by
  rw [show D2M8K2.u9983 = KTree.node D2M8K2.t9988 (nat_lit 21319533) (nat_lit 1392942350) (nat_lit 0) D2M8K2.t9989 from rfl, totK_node, tot9988, tot9989]
  decide +kernel

theorem arows9984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9984 = true := by
  rw [show D2M8K2.u9984 = KTree.node D2M8K2.t9990 (nat_lit 21321387) (nat_lit 3727771151) (nat_lit 0) D2M8K2.t9991 from rfl, allE_node, rows9990, irow9984, rows9991]
  all_goals rfl

theorem atot9984 : totK PD2M8K2 D2M8K2.u9984 = [0, 0, 189980759500, 858170174995, 699020505791, 65457999967, 0, 0] := by
  rw [show D2M8K2.u9984 = KTree.node D2M8K2.t9990 (nat_lit 21321387) (nat_lit 3727771151) (nat_lit 0) D2M8K2.t9991 from rfl, totK_node, tot9990, tot9991]
  decide +kernel

theorem arows9987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9987 = true := by
  rw [show D2M8K2.u9987 = KTree.node D2M8K2.t9992 (nat_lit 21324108) (nat_lit 3563894132) (nat_lit 0) D2M8K2.t9993 from rfl, allE_node, rows9992, irow9987, rows9993]
  all_goals rfl

theorem atot9987 : totK PD2M8K2 D2M8K2.u9987 = [0, 0, 356596199807, 863486058901, 489392530738, 69844550520, 1409560813, 0] := by
  rw [show D2M8K2.u9987 = KTree.node D2M8K2.t9992 (nat_lit 21324108) (nat_lit 3563894132) (nat_lit 0) D2M8K2.t9993 from rfl, totK_node, tot9992, tot9993]
  decide +kernel

theorem arows9988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9988 = true := by
  rw [show D2M8K2.u9988 = KTree.node D2M8K2.t9994 (nat_lit 21326405) (nat_lit 2299794389) (nat_lit 0) D2M8K2.t9995 from rfl, allE_node, rows9994, irow9988, rows9995]
  all_goals rfl

theorem atot9988 : totK PD2M8K2 D2M8K2.u9988 = [0, 0, 168585381551, 766768386818, 753012291294, 80969800545, 1164319620, 0] := by
  rw [show D2M8K2.u9988 = KTree.node D2M8K2.t9994 (nat_lit 21326405) (nat_lit 2299794389) (nat_lit 0) D2M8K2.t9995 from rfl, totK_node, tot9994, tot9995]
  decide +kernel

theorem arows9990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9990 = true := by
  rw [show D2M8K2.u9990 = KTree.node D2M8K2.t9996 (nat_lit 21328224) (nat_lit 3540521261) (nat_lit 0) D2M8K2.t9997 from rfl, allE_node, rows9996, irow9990, rows9997]
  all_goals rfl

theorem atot9990 : totK PD2M8K2 D2M8K2.u9990 = [0, 0, 261076639762, 816968802809, 627784384452, 86801103237, 1198073392, 0] := by
  rw [show D2M8K2.u9990 = KTree.node D2M8K2.t9996 (nat_lit 21328224) (nat_lit 3540521261) (nat_lit 0) D2M8K2.t9997 from rfl, totK_node, tot9996, tot9997]
  decide +kernel

theorem arows9991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9991 = true := by
  rw [show D2M8K2.u9991 = KTree.node D2M8K2.t9998 (nat_lit 21329965) (nat_lit 1117531284) (nat_lit 0) D2M8K2.t9999 from rfl, allE_node, rows9998, irow9991, rows9999]
  all_goals rfl

theorem atot9991 : totK PD2M8K2 D2M8K2.u9991 = [0, 0, 141325792250, 626026612405, 786010256912, 214118793119, 11986244008, 0] := by
  rw [show D2M8K2.u9991 = KTree.node D2M8K2.t9998 (nat_lit 21329965) (nat_lit 1117531284) (nat_lit 0) D2M8K2.t9999 from rfl, totK_node, tot9998, tot9999]
  decide +kernel

theorem arows9995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9995 = true := by
  rw [show D2M8K2.u9995 = KTree.node D2M8K2.t10000 (nat_lit 21331398) (nat_lit 3878967719) (nat_lit 0) D2M8K2.t10001 from rfl, allE_node, rows10000, irow9995, rows10001]
  all_goals rfl

theorem atot9995 : totK PD2M8K2 D2M8K2.u9995 = [0, 0, 293064132822, 885757152275, 569110054641, 49143666701, 0, 0] := by
  rw [show D2M8K2.u9995 = KTree.node D2M8K2.t10000 (nat_lit 21331398) (nat_lit 3878967719) (nat_lit 0) D2M8K2.t10001 from rfl, totK_node, tot10000, tot10001]
  decide +kernel

theorem arows9996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9996 = true := by
  rw [show D2M8K2.u9996 = KTree.node D2M8K2.t10002 (nat_lit 21333351) (nat_lit 2550732713) (nat_lit 32) D2M8K2.t10003 from rfl, allE_node, rows10002, irow9996, rows10003]
  all_goals rfl

theorem atot9996 : totK PD2M8K2 D2M8K2.u9996 = [0, 0, 155536724975, 662470935696, 798298434016, 168727779819, 4980514959, 0] := by
  rw [show D2M8K2.u9996 = KTree.node D2M8K2.t10002 (nat_lit 21333351) (nat_lit 2550732713) (nat_lit 32) D2M8K2.t10003 from rfl, totK_node, tot10002, tot10003]
  decide +kernel

theorem arows9998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9998 = true := by
  rw [show D2M8K2.u9998 = KTree.node D2M8K2.t10004 (nat_lit 21359386) (nat_lit 2827550103) (nat_lit 0) D2M8K2.t10005 from rfl, allE_node, rows10004, irow9998, rows10005]
  all_goals rfl

theorem atot9998 : totK PD2M8K2 D2M8K2.u9998 = [0, 0, 261902276818, 830276710916, 593033136341, 80760488041, 1369150432, 0] := by
  rw [show D2M8K2.u9998 = KTree.node D2M8K2.t10004 (nat_lit 21359386) (nat_lit 2827550103) (nat_lit 0) D2M8K2.t10005 from rfl, totK_node, tot10004, tot10005]
  decide +kernel

theorem arows9999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u9999 = true := by
  rw [show D2M8K2.u9999 = KTree.node D2M8K2.t10006 (nat_lit 21361374) (nat_lit 3894591339) (nat_lit 0) D2M8K2.t10007 from rfl, allE_node, rows10006, irow9999, rows10007]
  all_goals rfl

theorem atot9999 : totK PD2M8K2 D2M8K2.u9999 = [0, 0, 183557299978, 759821651637, 784515072883, 99377542625, 0, 0] := by
  rw [show D2M8K2.u9999 = KTree.node D2M8K2.t10006 (nat_lit 21361374) (nat_lit 3894591339) (nat_lit 0) D2M8K2.t10007 from rfl, totK_node, tot10006, tot10007]
  decide +kernel

theorem arows10002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10002 = true := by
  rw [show D2M8K2.u10002 = KTree.node D2M8K2.t10008 (nat_lit 21365061) (nat_lit 1500051849) (nat_lit 0) D2M8K2.t10009 from rfl, allE_node, rows10008, irow10002, rows10009]
  all_goals rfl

theorem atot10002 : totK PD2M8K2 D2M8K2.u10002 = [0, 0, 386164287763, 948249633755, 475971247653, 33819428054, 0, 0] := by
  rw [show D2M8K2.u10002 = KTree.node D2M8K2.t10008 (nat_lit 21365061) (nat_lit 1500051849) (nat_lit 0) D2M8K2.t10009 from rfl, totK_node, tot10008, tot10009]
  decide +kernel

theorem arows10003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10003 = true := by
  rw [show D2M8K2.u10003 = KTree.node D2M8K2.t10010 (nat_lit 21368533) (nat_lit 1267650260) (nat_lit 0) D2M8K2.t10011 from rfl, allE_node, rows10010, irow10003, rows10011]
  all_goals rfl

theorem atot10003 : totK PD2M8K2 D2M8K2.u10003 = [0, 0, 378991084411, 921806511529, 483070851608, 37637136654, 0, 0] := by
  rw [show D2M8K2.u10003 = KTree.node D2M8K2.t10010 (nat_lit 21368533) (nat_lit 1267650260) (nat_lit 0) D2M8K2.t10011 from rfl, totK_node, tot10010, tot10011]
  decide +kernel

theorem arows10005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10005 = true := by
  rw [show D2M8K2.u10005 = KTree.node D2M8K2.t10012 (nat_lit 21370067) (nat_lit 2881648733) (nat_lit 0) D2M8K2.t10013 from rfl, allE_node, rows10012, irow10005, rows10013]
  all_goals rfl

theorem atot10005 : totK PD2M8K2 D2M8K2.u10005 = [0, 0, 175740758571, 769741477452, 753619770796, 114156795880, 1162515529, 0] := by
  rw [show D2M8K2.u10005 = KTree.node D2M8K2.t10012 (nat_lit 21370067) (nat_lit 2881648733) (nat_lit 0) D2M8K2.t10013 from rfl, totK_node, tot10012, tot10013]
  decide +kernel

theorem arows10006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10006 = true := by
  rw [show D2M8K2.u10006 = KTree.node D2M8K2.t10014 (nat_lit 21375516) (nat_lit 3510032231) (nat_lit 0) D2M8K2.t10015 from rfl, allE_node, rows10014, irow10006, rows10015]
  all_goals rfl

theorem atot10006 : totK PD2M8K2 D2M8K2.u10006 = [0, 0, 257950227735, 784488136756, 648586830455, 124366355250, 4030866388, 0] := by
  rw [show D2M8K2.u10006 = KTree.node D2M8K2.t10014 (nat_lit 21375516) (nat_lit 3510032231) (nat_lit 0) D2M8K2.t10015 from rfl, totK_node, tot10014, tot10015]
  decide +kernel

theorem arows10011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10011 = true := by
  rw [show D2M8K2.u10011 = KTree.node D2M8K2.t10016 (nat_lit 21377009) (nat_lit 1581600980) (nat_lit 0) D2M8K2.t10017 from rfl, allE_node, rows10016, irow10011, rows10017]
  all_goals rfl

theorem atot10011 : totK PD2M8K2 D2M8K2.u10011 = [0, 0, 181341888804, 778322724248, 747734554614, 117392249323, 1249641317, 0] := by
  rw [show D2M8K2.u10011 = KTree.node D2M8K2.t10016 (nat_lit 21377009) (nat_lit 1581600980) (nat_lit 0) D2M8K2.t10017 from rfl, totK_node, tot10016, tot10017]
  decide +kernel

theorem arows10012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10012 = true := by
  rw [show D2M8K2.u10012 = KTree.node D2M8K2.t10018 (nat_lit 21444840) (nat_lit 2770468919) (nat_lit 0) D2M8K2.t10019 from rfl, allE_node, rows10018, irow10012, rows10019]
  all_goals rfl

theorem atot10012 : totK PD2M8K2 D2M8K2.u10012 = [0, 216021588155, 507794237260, 450456958632, 446900981925, 187837707555, 12680748845, 0] := by
  rw [show D2M8K2.u10012 = KTree.node D2M8K2.t10018 (nat_lit 21444840) (nat_lit 2770468919) (nat_lit 0) D2M8K2.t10019 from rfl, totK_node, tot10018, tot10019]
  decide +kernel

theorem arows10014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10014 = true := by
  rw [show D2M8K2.u10014 = KTree.node D2M8K2.t10020 (nat_lit 21445982) (nat_lit 3889182706) (nat_lit 0) D2M8K2.t10021 from rfl, allE_node, rows10020, irow10014, rows10021]
  all_goals rfl

theorem atot10014 : totK PD2M8K2 D2M8K2.u10014 = [0, 233409488757, 773198307480, 622125356878, 190264359573, 21400436502, 0, 0] := by
  rw [show D2M8K2.u10014 = KTree.node D2M8K2.t10020 (nat_lit 21445982) (nat_lit 3889182706) (nat_lit 0) D2M8K2.t10021 from rfl, totK_node, tot10020, tot10021]
  decide +kernel

theorem arows10015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10015 = true := by
  rw [show D2M8K2.u10015 = KTree.node D2M8K2.t10022 (nat_lit 21447430) (nat_lit 3037135374) (nat_lit 0) D2M8K2.t10023 from rfl, allE_node, rows10022, irow10015, rows10023]
  all_goals rfl

theorem atot10015 : totK PD2M8K2 D2M8K2.u10015 = [0, 51340655322, 446348102772, 894070714788, 395484781486, 16208961603, 0, 0] := by
  rw [show D2M8K2.u10015 = KTree.node D2M8K2.t10022 (nat_lit 21447430) (nat_lit 3037135374) (nat_lit 0) D2M8K2.t10023 from rfl, totK_node, tot10022, tot10023]
  decide +kernel

theorem arows10018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10018 = true := by
  rw [show D2M8K2.u10018 = KTree.node D2M8K2.t10024 (nat_lit 21448766) (nat_lit 2481229240) (nat_lit 0) D2M8K2.t10025 from rfl, allE_node, rows10024, irow10018, rows10025]
  all_goals rfl

theorem atot10018 : totK PD2M8K2 D2M8K2.u10018 = [0, 352835989509, 911345152871, 521056498699, 40924751648, 0, 0, 0] := by
  rw [show D2M8K2.u10018 = KTree.node D2M8K2.t10024 (nat_lit 21448766) (nat_lit 2481229240) (nat_lit 0) D2M8K2.t10025 from rfl, totK_node, tot10024, tot10025]
  decide +kernel

theorem arows10019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10019 = true := by
  rw [show D2M8K2.u10019 = KTree.node D2M8K2.t10026 (nat_lit 21450514) (nat_lit 4039915514) (nat_lit 0) D2M8K2.t10027 from rfl, allE_node, rows10026, irow10019, rows10027]
  all_goals rfl

theorem atot10019 : totK PD2M8K2 D2M8K2.u10019 = [0, 67565028568, 548071713551, 891385514190, 259655184861, 9087311183, 0, 0] := by
  rw [show D2M8K2.u10019 = KTree.node D2M8K2.t10026 (nat_lit 21450514) (nat_lit 4039915514) (nat_lit 0) D2M8K2.t10027 from rfl, totK_node, tot10026, tot10027]
  decide +kernel

theorem arows10021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10021 = true := by
  rw [show D2M8K2.u10021 = KTree.node D2M8K2.t10028 (nat_lit 21452496) (nat_lit 3310179290) (nat_lit 0) D2M8K2.t10029 from rfl, allE_node, rows10028, irow10021, rows10029]
  all_goals rfl

theorem atot10021 : totK PD2M8K2 D2M8K2.u10021 = [0, 356072225375, 929886524689, 513864431284, 40729668995, 0, 0, 0] := by
  rw [show D2M8K2.u10021 = KTree.node D2M8K2.t10028 (nat_lit 21452496) (nat_lit 3310179290) (nat_lit 0) D2M8K2.t10029 from rfl, totK_node, tot10028, tot10029]
  decide +kernel

theorem arows10022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10022 = true := by
  rw [show D2M8K2.u10022 = KTree.node D2M8K2.t10030 (nat_lit 21454160) (nat_lit 3474487832) (nat_lit 0) D2M8K2.t10031 from rfl, allE_node, rows10030, irow10022, rows10031]
  all_goals rfl

theorem atot10022 : totK PD2M8K2 D2M8K2.u10022 = [0, 46925638102, 498036452310, 921897274207, 300226883909, 13194699740, 0, 0] := by
  rw [show D2M8K2.u10022 = KTree.node D2M8K2.t10030 (nat_lit 21454160) (nat_lit 3474487832) (nat_lit 0) D2M8K2.t10031 from rfl, totK_node, tot10030, tot10031]
  decide +kernel

theorem arows10026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10026 = true := by
  rw [show D2M8K2.u10026 = KTree.node D2M8K2.t10032 (nat_lit 21455568) (nat_lit 2633679534) (nat_lit 0) D2M8K2.t10033 from rfl, allE_node, rows10032, irow10026, rows10033]
  all_goals rfl

theorem atot10026 : totK PD2M8K2 D2M8K2.u10026 = [0, 370672401406, 926943438196, 482949561575, 39329787620, 0, 0, 0] := by
  rw [show D2M8K2.u10026 = KTree.node D2M8K2.t10032 (nat_lit 21455568) (nat_lit 2633679534) (nat_lit 0) D2M8K2.t10033 from rfl, totK_node, tot10032, tot10033]
  decide +kernel

theorem arows10027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10027 = true := by
  rw [show D2M8K2.u10027 = KTree.node D2M8K2.t10034 (nat_lit 21457441) (nat_lit 1431932430) (nat_lit 0) D2M8K2.t10035 from rfl, allE_node, rows10034, irow10027, rows10035]
  all_goals rfl

theorem atot10027 : totK PD2M8K2 D2M8K2.u10027 = [0, 66761380721, 623625237100, 904950014940, 189799797716, 3867150671, 0, 0] := by
  rw [show D2M8K2.u10027 = KTree.node D2M8K2.t10034 (nat_lit 21457441) (nat_lit 1431932430) (nat_lit 0) D2M8K2.t10035 from rfl, totK_node, tot10034, tot10035]
  decide +kernel

theorem arows10029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10029 = true := by
  rw [show D2M8K2.u10029 = KTree.node D2M8K2.t10036 (nat_lit 21459093) (nat_lit 1435445072) (nat_lit 0) D2M8K2.t10037 from rfl, allE_node, rows10036, irow10029, rows10037]
  all_goals rfl

theorem atot10029 : totK PD2M8K2 D2M8K2.u10029 = [0, 356129927677, 923415579736, 514151521325, 41817993249, 0, 0, 0] := by
  rw [show D2M8K2.u10029 = KTree.node D2M8K2.t10036 (nat_lit 21459093) (nat_lit 1435445072) (nat_lit 0) D2M8K2.t10037 from rfl, totK_node, tot10036, tot10037]
  decide +kernel

theorem arows10030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10030 = true := by
  rw [show D2M8K2.u10030 = KTree.node D2M8K2.t10038 (nat_lit 21460761) (nat_lit 564039528) (nat_lit 0) D2M8K2.t10039 from rfl, allE_node, rows10038, irow10030, rows10039]
  all_goals rfl

theorem atot10030 : totK PD2M8K2 D2M8K2.u10030 = [0, 0, 443936814480, 983516516054, 337166686514, 8620084670, 0, 0] := by
  rw [show D2M8K2.u10030 = KTree.node D2M8K2.t10038 (nat_lit 21460761) (nat_lit 564039528) (nat_lit 0) D2M8K2.t10039 from rfl, totK_node, tot10038, tot10039]
  decide +kernel

theorem arows10033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10033 = true := by
  rw [show D2M8K2.u10033 = KTree.node D2M8K2.t10040 (nat_lit 21465964) (nat_lit 3922965962) (nat_lit 0) D2M8K2.t10041 from rfl, allE_node, rows10040, irow10033, rows10041]
  all_goals rfl

theorem atot10033 : totK PD2M8K2 D2M8K2.u10033 = [0, 0, 358699431936, 914878001024, 525537364718, 46118264520, 0, 0] := by
  rw [show D2M8K2.u10033 = KTree.node D2M8K2.t10040 (nat_lit 21465964) (nat_lit 3922965962) (nat_lit 0) D2M8K2.t10041 from rfl, totK_node, tot10040, tot10041]
  decide +kernel

theorem arows10034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10034 = true := by
  rw [show D2M8K2.u10034 = KTree.node D2M8K2.t10042 (nat_lit 21467449) (nat_lit 760516232) (nat_lit 0) D2M8K2.t10043 from rfl, allE_node, rows10042, irow10034, rows10043]
  all_goals rfl

theorem atot10034 : totK PD2M8K2 D2M8K2.u10034 = [0, 0, 89209449686, 533503800493, 826490344718, 337793990414, 27952737642, 0] := by
  rw [show D2M8K2.u10034 = KTree.node D2M8K2.t10042 (nat_lit 21467449) (nat_lit 760516232) (nat_lit 0) D2M8K2.t10043 from rfl, totK_node, tot10042, tot10043]
  decide +kernel

theorem arows10036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10036 = true := by
  rw [show D2M8K2.u10036 = KTree.node D2M8K2.t10044 (nat_lit 21468770) (nat_lit 3118063970) (nat_lit 0) D2M8K2.t10045 from rfl, allE_node, rows10044, irow10036, rows10045]
  all_goals rfl

theorem atot10036 : totK PD2M8K2 D2M8K2.u10036 = [0, 0, 231985960101, 676640030197, 673426948850, 226019507251, 8969136212, 0] := by
  rw [show D2M8K2.u10036 = KTree.node D2M8K2.t10044 (nat_lit 21468770) (nat_lit 3118063970) (nat_lit 0) D2M8K2.t10045 from rfl, totK_node, tot10044, tot10045]
  decide +kernel

theorem arows10037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10037 = true := by
  rw [show D2M8K2.u10037 = KTree.node D2M8K2.t10046 (nat_lit 21470286) (nat_lit 3602804972) (nat_lit 0) D2M8K2.t10047 from rfl, allE_node, rows10046, irow10037, rows10047]
  all_goals rfl

theorem atot10037 : totK PD2M8K2 D2M8K2.u10037 = [0, 0, 170267687701, 752299917078, 733264771802, 124494675973, 4009909289, 0] := by
  rw [show D2M8K2.u10037 = KTree.node D2M8K2.t10046 (nat_lit 21470286) (nat_lit 3602804972) (nat_lit 0) D2M8K2.t10047 from rfl, totK_node, tot10046, tot10047]
  decide +kernel

theorem arows10043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10043 = true := by
  rw [show D2M8K2.u10043 = KTree.node D2M8K2.t10048 (nat_lit 21472444) (nat_lit 3768311409) (nat_lit 0) D2M8K2.t10049 from rfl, allE_node, rows10048, irow10043, rows10049]
  all_goals rfl

theorem atot10043 : totK PD2M8K2 D2M8K2.u10043 = [0, 0, 249274693814, 786127316569, 674330921042, 105767597909, 1149959346, 0] := by
  rw [show D2M8K2.u10043 = KTree.node D2M8K2.t10048 (nat_lit 21472444) (nat_lit 3768311409) (nat_lit 0) D2M8K2.t10049 from rfl, totK_node, tot10048, tot10049]
  decide +kernel

theorem arows10044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10044 = true := by
  rw [show D2M8K2.u10044 = KTree.node D2M8K2.t10050 (nat_lit 21473862) (nat_lit 3800508143) (nat_lit 0) D2M8K2.t10051 from rfl, allE_node, rows10050, irow10044, rows10051]
  all_goals rfl

theorem atot10044 : totK PD2M8K2 D2M8K2.u10044 = [0, 0, 172446104734, 747406118275, 726408227072, 143540204175, 4031931762, 0] := by
  rw [show D2M8K2.u10044 = KTree.node D2M8K2.t10050 (nat_lit 21473862) (nat_lit 3800508143) (nat_lit 0) D2M8K2.t10051 from rfl, totK_node, tot10050, tot10051]
  decide +kernel

theorem arows10046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10046 = true := by
  rw [show D2M8K2.u10046 = KTree.node D2M8K2.t10052 (nat_lit 21475953) (nat_lit 1835327690) (nat_lit 0) D2M8K2.t10053 from rfl, allE_node, rows10052, irow10046, rows10053]
  all_goals rfl

theorem atot10046 : totK PD2M8K2 D2M8K2.u10046 = [0, 0, 280063637893, 793860541570, 613249986671, 104246962858, 1186940923, 0] := by
  rw [show D2M8K2.u10046 = KTree.node D2M8K2.t10052 (nat_lit 21475953) (nat_lit 1835327690) (nat_lit 0) D2M8K2.t10053 from rfl, totK_node, tot10052, tot10053]
  decide +kernel

theorem arows10047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10047 = true := by
  rw [show D2M8K2.u10047 = KTree.node D2M8K2.t10054 (nat_lit 21477420) (nat_lit 3092463159) (nat_lit 0) D2M8K2.t10055 from rfl, allE_node, rows10054, irow10047, rows10055]
  all_goals rfl

theorem atot10047 : totK PD2M8K2 D2M8K2.u10047 = [0, 0, 131561998149, 781627845992, 804107519028, 84281913627, 0, 0] := by
  rw [show D2M8K2.u10047 = KTree.node D2M8K2.t10054 (nat_lit 21477420) (nat_lit 3092463159) (nat_lit 0) D2M8K2.t10055 from rfl, totK_node, tot10054, tot10055]
  decide +kernel

theorem arows10050 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10050 = true := by
  rw [show D2M8K2.u10050 = KTree.node D2M8K2.t10056 (nat_lit 21479566) (nat_lit 3611688590) (nat_lit 0) D2M8K2.t10057 from rfl, allE_node, rows10056, irow10050, rows10057]
  all_goals rfl

theorem atot10050 : totK PD2M8K2 D2M8K2.u10050 = [0, 0, 328405174544, 845516453996, 548848536907, 93066882933, 1415142070, 0] := by
  rw [show D2M8K2.u10050 = KTree.node D2M8K2.t10056 (nat_lit 21479566) (nat_lit 3611688590) (nat_lit 0) D2M8K2.t10057 from rfl, totK_node, tot10056, tot10057]
  decide +kernel

theorem arows10051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10051 = true := by
  rw [show D2M8K2.u10051 = KTree.node D2M8K2.t10058 (nat_lit 21481360) (nat_lit 3370314378) (nat_lit 0) D2M8K2.t10059 from rfl, allE_node, rows10058, irow10051, rows10059]
  all_goals rfl

theorem atot10051 : totK PD2M8K2 D2M8K2.u10051 = [0, 0, 92515481918, 644230092251, 865215022482, 190683664401, 2484078857, 0] := by
  rw [show D2M8K2.u10051 = KTree.node D2M8K2.t10058 (nat_lit 21481360) (nat_lit 3370314378) (nat_lit 0) D2M8K2.t10059 from rfl, totK_node, tot10058, tot10059]
  decide +kernel

theorem arows10053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10053 = true := by
  rw [show D2M8K2.u10053 = KTree.node D2M8K2.t10060 (nat_lit 21486628) (nat_lit 3861555415) (nat_lit 0) D2M8K2.t10061 from rfl, allE_node, rows10060, irow10053, rows10061]
  all_goals rfl

theorem atot10053 : totK PD2M8K2 D2M8K2.u10053 = [0, 341777962925, 806929782205, 432099465390, 152581121628, 90561717777, 6818291842, 0] := by
  rw [show D2M8K2.u10053 = KTree.node D2M8K2.t10060 (nat_lit 21486628) (nat_lit 3861555415) (nat_lit 0) D2M8K2.t10061 from rfl, totK_node, tot10060, tot10061]
  decide +kernel

theorem arows10054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10054 = true := by
  rw [show D2M8K2.u10054 = KTree.node D2M8K2.t10062 (nat_lit 21488153) (nat_lit 1693077601) (nat_lit 0) D2M8K2.t10063 from rfl, allE_node, rows10062, irow10054, rows10063]
  all_goals rfl

theorem atot10054 : totK PD2M8K2 D2M8K2.u10054 = [0, 87744675159, 553907583516, 817673158759, 336279337306, 28243088426, 0, 0] := by
  rw [show D2M8K2.u10054 = KTree.node D2M8K2.t10062 (nat_lit 21488153) (nat_lit 1693077601) (nat_lit 0) D2M8K2.t10063 from rfl, totK_node, tot10062, tot10063]
  decide +kernel

theorem arows10058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10058 = true := by
  rw [show D2M8K2.u10058 = KTree.node D2M8K2.t10064 (nat_lit 21489413) (nat_lit 2330038851) (nat_lit 0) D2M8K2.t10065 from rfl, allE_node, rows10064, irow10058, rows10065]
  all_goals rfl

theorem atot10058 : totK PD2M8K2 D2M8K2.u10058 = [0, 197639695054, 644053549345, 714819332896, 249719162552, 9354028391, 0, 0] := by
  rw [show D2M8K2.u10058 = KTree.node D2M8K2.t10064 (nat_lit 21489413) (nat_lit 2330038851) (nat_lit 0) D2M8K2.t10065 from rfl, totK_node, tot10064, tot10065]
  decide +kernel

theorem arows10059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10059 = true := by
  rw [show D2M8K2.u10059 = KTree.node D2M8K2.t10066 (nat_lit 21490912) (nat_lit 3756584681) (nat_lit 0) D2M8K2.t10067 from rfl, allE_node, rows10066, irow10059, rows10067]
  all_goals rfl

theorem atot10059 : totK PD2M8K2 D2M8K2.u10059 = [0, 225478932148, 836791505049, 674611659936, 79097190958, 0, 0, 0] := by
  rw [show D2M8K2.u10059 = KTree.node D2M8K2.t10066 (nat_lit 21490912) (nat_lit 3756584681) (nat_lit 0) D2M8K2.t10067 from rfl, totK_node, tot10066, tot10067]
  decide +kernel

theorem arows10061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10061 = true := by
  rw [show D2M8K2.u10061 = KTree.node D2M8K2.t10068 (nat_lit 21492714) (nat_lit 3552414217) (nat_lit 0) D2M8K2.t10069 from rfl, allE_node, rows10068, irow10061, rows10069]
  all_goals rfl

theorem atot10061 : totK PD2M8K2 D2M8K2.u10061 = [0, 189698210248, 659628177686, 723185968162, 210117215110, 11885407614, 0, 0] := by
  rw [show D2M8K2.u10061 = KTree.node D2M8K2.t10068 (nat_lit 21492714) (nat_lit 3552414217) (nat_lit 0) D2M8K2.t10069 from rfl, totK_node, tot10068, tot10069]
  decide +kernel

theorem arows10062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10062 = true := by
  rw [show D2M8K2.u10062 = KTree.node D2M8K2.t10070 (nat_lit 21497576) (nat_lit 3950786586) (nat_lit 0) D2M8K2.t10071 from rfl, allE_node, rows10070, irow10062, rows10071]
  all_goals rfl

theorem atot10062 : totK PD2M8K2 D2M8K2.u10062 = [0, 210332088383, 829940783725, 691144854370, 73297929757, 0, 0, 0] := by
  rw [show D2M8K2.u10062 = KTree.node D2M8K2.t10070 (nat_lit 21497576) (nat_lit 3950786586) (nat_lit 0) D2M8K2.t10071 from rfl, totK_node, tot10070, tot10071]
  decide +kernel

theorem arows10065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10065 = true := by
  rw [show D2M8K2.u10065 = KTree.node D2M8K2.t10072 (nat_lit 21500108) (nat_lit 3554347748) (nat_lit 0) D2M8K2.t10073 from rfl, allE_node, rows10072, irow10065, rows10073]
  all_goals rfl

theorem atot10065 : totK PD2M8K2 D2M8K2.u10065 = [0, 258218038009, 774268753034, 649331819574, 133074643811, 3884009855, 0, 0] := by
  rw [show D2M8K2.u10065 = KTree.node D2M8K2.t10072 (nat_lit 21500108) (nat_lit 3554347748) (nat_lit 0) D2M8K2.t10073 from rfl, totK_node, tot10072, tot10073]
  decide +kernel

theorem arows10066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10066 = true := by
  rw [show D2M8K2.u10066 = KTree.node D2M8K2.t10074 (nat_lit 21501587) (nat_lit 2547295459) (nat_lit 32) D2M8K2.t10075 from rfl, allE_node, rows10074, irow10066, rows10075]
  all_goals rfl

theorem atot10066 : totK PD2M8K2 D2M8K2.u10066 = [0, 147558936287, 669231272964, 787608683491, 194972397465, 4967996017, 0, 0] := by
  rw [show D2M8K2.u10066 = KTree.node D2M8K2.t10074 (nat_lit 21501587) (nat_lit 2547295459) (nat_lit 32) D2M8K2.t10075 from rfl, totK_node, tot10074, tot10075]
  decide +kernel

theorem arows10068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10068 = true := by
  rw [show D2M8K2.u10068 = KTree.node D2M8K2.t10076 (nat_lit 21507079) (nat_lit 2251334374) (nat_lit 0) D2M8K2.t10077 from rfl, allE_node, rows10076, irow10068, rows10077]
  all_goals rfl

theorem atot10068 : totK PD2M8K2 D2M8K2.u10068 = [0, 0, 372348530358, 930232853011, 483865490647, 42010839919, 0, 0] := by
  rw [show D2M8K2.u10068 = KTree.node D2M8K2.t10076 (nat_lit 21507079) (nat_lit 2251334374) (nat_lit 0) D2M8K2.t10077 from rfl, totK_node, tot10076, tot10077]
  decide +kernel

theorem arows10069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10069 = true := by
  rw [show D2M8K2.u10069 = KTree.node D2M8K2.t10078 (nat_lit 21508322) (nat_lit 3991730768) (nat_lit 0) D2M8K2.t10079 from rfl, allE_node, rows10078, irow10069, rows10079]
  all_goals rfl

theorem atot10069 : totK PD2M8K2 D2M8K2.u10069 = [0, 0, 349193849454, 949151845288, 486539259525, 29781284155, 0, 0] := by
  rw [show D2M8K2.u10069 = KTree.node D2M8K2.t10078 (nat_lit 21508322) (nat_lit 3991730768) (nat_lit 0) D2M8K2.t10079 from rfl, totK_node, tot10078, tot10079]
  decide +kernel

theorem arows10074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10074 = true := by
  rw [show D2M8K2.u10074 = KTree.node D2M8K2.t10080 (nat_lit 21511593) (nat_lit 1348561873) (nat_lit 0) D2M8K2.t10081 from rfl, allE_node, rows10080, irow10074, rows10081]
  all_goals rfl

theorem atot10074 : totK PD2M8K2 D2M8K2.u10074 = [0, 0, 264722091586, 872471530123, 608695039488, 52710598832, 0, 0] := by
  rw [show D2M8K2.u10074 = KTree.node D2M8K2.t10080 (nat_lit 21511593) (nat_lit 1348561873) (nat_lit 0) D2M8K2.t10081 from rfl, totK_node, tot10080, tot10081]
  decide +kernel

theorem arows10075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10075 = true := by
  rw [show D2M8K2.u10075 = KTree.node D2M8K2.t10082 (nat_lit 21517068) (nat_lit 3603536935) (nat_lit 0) D2M8K2.t10083 from rfl, allE_node, rows10082, irow10075, rows10083]
  all_goals rfl

theorem atot10075 : totK PD2M8K2 D2M8K2.u10075 = [0, 0, 226741266677, 702553957769, 670578568346, 165902107954, 5717851365, 0] := by
  rw [show D2M8K2.u10075 = KTree.node D2M8K2.t10082 (nat_lit 21517068) (nat_lit 3603536935) (nat_lit 0) D2M8K2.t10083 from rfl, totK_node, tot10082, tot10083]
  decide +kernel

theorem arows10077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10077 = true := by
  rw [show D2M8K2.u10077 = KTree.node D2M8K2.t10084 (nat_lit 21518409) (nat_lit 1843620068) (nat_lit 0) D2M8K2.t10085 from rfl, allE_node, rows10084, irow10077, rows10085]
  all_goals rfl

theorem atot10077 : totK PD2M8K2 D2M8K2.u10077 = [0, 0, 172390137915, 847942052368, 685651255557, 55944661521, 0, 0] := by
  rw [show D2M8K2.u10077 = KTree.node D2M8K2.t10084 (nat_lit 21518409) (nat_lit 1843620068) (nat_lit 0) D2M8K2.t10085 from rfl, totK_node, tot10084, tot10085]
  decide +kernel

theorem arows10078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10078 = true := by
  rw [show D2M8K2.u10078 = KTree.node D2M8K2.t10086 (nat_lit 21520994) (nat_lit 4097537282) (nat_lit 0) D2M8K2.t10087 from rfl, allE_node, rows10086, irow10078, rows10087]
  all_goals rfl

theorem atot10078 : totK PD2M8K2 D2M8K2.u10078 = [0, 0, 313179289438, 835385420466, 556159995481, 84836801313, 1330264907, 0] := by
  rw [show D2M8K2.u10078 = KTree.node D2M8K2.t10086 (nat_lit 21520994) (nat_lit 4097537282) (nat_lit 0) D2M8K2.t10087 from rfl, totK_node, tot10086, tot10087]
  decide +kernel

theorem arows10081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10081 = true := by
  rw [show D2M8K2.u10081 = KTree.node D2M8K2.t10088 (nat_lit 21524839) (nat_lit 2392624099) (nat_lit 0) D2M8K2.t10089 from rfl, allE_node, rows10088, irow10081, rows10089]
  all_goals rfl

theorem atot10081 : totK PD2M8K2 D2M8K2.u10081 = [0, 290240873679, 797492730133, 548000035848, 165394635854, 13552619715, 0, 0] := by
  rw [show D2M8K2.u10081 = KTree.node D2M8K2.t10088 (nat_lit 21524839) (nat_lit 2392624099) (nat_lit 0) D2M8K2.t10089 from rfl, totK_node, tot10088, tot10089]
  decide +kernel

theorem arows10082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10082 = true := by
  rw [show D2M8K2.u10082 = KTree.node D2M8K2.t10090 (nat_lit 21526674) (nat_lit 3440827476) (nat_lit 0) D2M8K2.t10091 from rfl, allE_node, rows10090, irow10082, rows10091]
  all_goals rfl

theorem atot10082 : totK PD2M8K2 D2M8K2.u10082 = [0, 144987525680, 708927880597, 833417878858, 140056339391, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10082 = KTree.node D2M8K2.t10090 (nat_lit 21526674) (nat_lit 3440827476) (nat_lit 0) D2M8K2.t10091 from rfl, totK_node, tot10090, tot10091]
  decide +kernel

theorem arows10084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10084 = true := by
  rw [show D2M8K2.u10084 = KTree.node D2M8K2.t10092 (nat_lit 21528576) (nat_lit 3278618670) (nat_lit 0) D2M8K2.t10093 from rfl, allE_node, rows10092, irow10084, rows10093]
  all_goals rfl

theorem atot10084 : totK PD2M8K2 D2M8K2.u10084 = [0, 336970107059, 922863246669, 531263671644, 39039826421, 0, 0, 0] := by
  rw [show D2M8K2.u10084 = KTree.node D2M8K2.t10092 (nat_lit 21528576) (nat_lit 3278618670) (nat_lit 0) D2M8K2.t10093 from rfl, totK_node, tot10092, tot10093]
  decide +kernel

theorem arows10085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10085 = true := by
  rw [show D2M8K2.u10085 = KTree.node D2M8K2.t10094 (nat_lit 21530056) (nat_lit 3295671183) (nat_lit 0) D2M8K2.t10095 from rfl, allE_node, rows10094, irow10085, rows10095]
  all_goals rfl

theorem atot10085 : totK PD2M8K2 D2M8K2.u10085 = [0, 0, 390007938053, 937052170157, 450857116023, 30795354140, 0, 0] := by
  rw [show D2M8K2.u10085 = KTree.node D2M8K2.t10094 (nat_lit 21530056) (nat_lit 3295671183) (nat_lit 0) D2M8K2.t10095 from rfl, totK_node, tot10094, tot10095]
  decide +kernel

theorem arows10089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10089 = true := by
  rw [show D2M8K2.u10089 = KTree.node D2M8K2.t10096 (nat_lit 21534802) (nat_lit 3970467854) (nat_lit 0) D2M8K2.t10097 from rfl, allE_node, rows10096, irow10089, rows10097]
  all_goals rfl

theorem atot10089 : totK PD2M8K2 D2M8K2.u10089 = [0, 353234853659, 830432483045, 522690445575, 130119811080, 6799735859, 0, 0] := by
  rw [show D2M8K2.u10089 = KTree.node D2M8K2.t10096 (nat_lit 21534802) (nat_lit 3970467854) (nat_lit 0) D2M8K2.t10097 from rfl, totK_node, tot10096, tot10097]
  decide +kernel

theorem arows10090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10090 = true := by
  rw [show D2M8K2.u10090 = KTree.node D2M8K2.t10098 (nat_lit 21536230) (nat_lit 2239516883) (nat_lit 0) D2M8K2.t10099 from rfl, allE_node, rows10098, irow10090, rows10099]
  all_goals rfl

theorem atot10090 : totK PD2M8K2 D2M8K2.u10090 = [0, 88383717769, 629762406151, 851490261494, 223774215960, 9668735432, 0, 0] := by
  rw [show D2M8K2.u10090 = KTree.node D2M8K2.t10098 (nat_lit 21536230) (nat_lit 2239516883) (nat_lit 0) D2M8K2.t10099 from rfl, totK_node, tot10098, tot10099]
  decide +kernel

theorem arows10092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10092 = true := by
  rw [show D2M8K2.u10092 = KTree.node D2M8K2.t10100 (nat_lit 21538114) (nat_lit 3843205375) (nat_lit 0) D2M8K2.t10101 from rfl, allE_node, rows10100, irow10092, rows10101]
  all_goals rfl

theorem atot10092 : totK PD2M8K2 D2M8K2.u10092 = [0, 268145134026, 768393329638, 628195617114, 126223904184, 3581949829, 0, 0] := by
  rw [show D2M8K2.u10092 = KTree.node D2M8K2.t10100 (nat_lit 21538114) (nat_lit 3843205375) (nat_lit 0) D2M8K2.t10101 from rfl, totK_node, tot10100, tot10101]
  decide +kernel

theorem arows10093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10093 = true := by
  rw [show D2M8K2.u10093 = KTree.node D2M8K2.t10102 (nat_lit 21539613) (nat_lit 1555880650) (nat_lit 0) D2M8K2.t10103 from rfl, allE_node, rows10102, irow10093, rows10103]
  all_goals rfl

theorem atot10093 : totK PD2M8K2 D2M8K2.u10093 = [0, 143616028299, 739403598052, 803960059905, 118778150528, 1096505104, 0, 0] := by
  rw [show D2M8K2.u10093 = KTree.node D2M8K2.t10102 (nat_lit 21539613) (nat_lit 1555880650) (nat_lit 0) D2M8K2.t10103 from rfl, totK_node, tot10102, tot10103]
  decide +kernel

theorem arows10096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10096 = true := by
  rw [show D2M8K2.u10096 = KTree.node D2M8K2.t10104 (nat_lit 21541639) (nat_lit 2305305579) (nat_lit 0) D2M8K2.t10105 from rfl, allE_node, rows10104, irow10096, rows10105]
  all_goals rfl

theorem atot10096 : totK PD2M8K2 D2M8K2.u10096 = [0, 324850495889, 824451480113, 551197888353, 116671357422, 3884009855, 0, 0] := by
  rw [show D2M8K2.u10096 = KTree.node D2M8K2.t10104 (nat_lit 21541639) (nat_lit 2305305579) (nat_lit 0) D2M8K2.t10105 from rfl, totK_node, tot10104, tot10105]
  decide +kernel

theorem arows10097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10097 = true := by
  rw [show D2M8K2.u10097 = KTree.node D2M8K2.t10106 (nat_lit 21543131) (nat_lit 2706212539) (nat_lit 0) D2M8K2.t10107 from rfl, allE_node, rows10106, irow10097, rows10107]
  all_goals rfl

theorem atot10097 : totK PD2M8K2 D2M8K2.u10097 = [0, 92333346222, 640003933356, 859496440192, 207176065377, 3687571860, 0, 0] := by
  rw [show D2M8K2.u10097 = KTree.node D2M8K2.t10106 (nat_lit 21543131) (nat_lit 2706212539) (nat_lit 0) D2M8K2.t10107 from rfl, totK_node, tot10106, tot10107]
  decide +kernel

theorem arows10099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10099 = true := by
  rw [show D2M8K2.u10099 = KTree.node D2M8K2.t10108 (nat_lit 21544847) (nat_lit 2754169071) (nat_lit 0) D2M8K2.t10109 from rfl, allE_node, rows10108, irow10099, rows10109]
  all_goals rfl

theorem atot10099 : totK PD2M8K2 D2M8K2.u10099 = [0, 0, 352282870285, 942220982371, 447510533624, 27864865103, 0, 0] := by
  rw [show D2M8K2.u10099 = KTree.node D2M8K2.t10108 (nat_lit 21544847) (nat_lit 2754169071) (nat_lit 0) D2M8K2.t10109 from rfl, totK_node, tot10108, tot10109]
  decide +kernel

theorem arows10100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10100 = true := by
  rw [show D2M8K2.u10100 = KTree.node D2M8K2.t10110 (nat_lit 21547314) (nat_lit 3437272954) (nat_lit 0) D2M8K2.t10111 from rfl, allE_node, rows10110, irow10100, rows10111]
  all_goals rfl

theorem atot10100 : totK PD2M8K2 D2M8K2.u10100 = [0, 0, 177365107145, 752971791867, 744303089615, 113171679162, 1239866073, 0] := by
  rw [show D2M8K2.u10100 = KTree.node D2M8K2.t10110 (nat_lit 21547314) (nat_lit 3437272954) (nat_lit 0) D2M8K2.t10111 from rfl, totK_node, tot10110, tot10111]
  decide +kernel

theorem arows10107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10107 = true := by
  rw [show D2M8K2.u10107 = KTree.node D2M8K2.t10112 (nat_lit 21549260) (nat_lit 3175557331) (nat_lit 0) D2M8K2.t10113 from rfl, allE_node, rows10112, irow10107, rows10113]
  all_goals rfl

theorem atot10107 : totK PD2M8K2 D2M8K2.u10107 = [0, 0, 335651543331, 928021942476, 523734767005, 35235256388, 0, 0] := by
  rw [show D2M8K2.u10107 = KTree.node D2M8K2.t10112 (nat_lit 21549260) (nat_lit 3175557331) (nat_lit 0) D2M8K2.t10113 from rfl, totK_node, tot10112, tot10113]
  decide +kernel

theorem arows10108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10108 = true := by
  rw [show D2M8K2.u10108 = KTree.node D2M8K2.t10114 (nat_lit 21555942) (nat_lit 3880930485) (nat_lit 0) D2M8K2.t10115 from rfl, allE_node, rows10114, irow10108, rows10115]
  all_goals rfl

theorem atot10108 : totK PD2M8K2 D2M8K2.u10108 = [0, 0, 373214997789, 930150108378, 473557031846, 38947731361, 0, 0] := by
  rw [show D2M8K2.u10108 = KTree.node D2M8K2.t10114 (nat_lit 21555942) (nat_lit 3880930485) (nat_lit 0) D2M8K2.t10115 from rfl, totK_node, tot10114, tot10115]
  decide +kernel

theorem arows10110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10110 = true := by
  rw [show D2M8K2.u10110 = KTree.node D2M8K2.t10116 (nat_lit 21557191) (nat_lit 2358564193) (nat_lit 0) D2M8K2.t10117 from rfl, allE_node, rows10116, irow10110, rows10117]
  all_goals rfl

theorem atot10110 : totK PD2M8K2 D2M8K2.u10110 = [0, 0, 63371571171, 539240993315, 862929399353, 266003560363, 11596263393, 0] := by
  rw [show D2M8K2.u10110 = KTree.node D2M8K2.t10116 (nat_lit 21557191) (nat_lit 2358564193) (nat_lit 0) D2M8K2.t10117 from rfl, totK_node, tot10116, tot10117]
  decide +kernel

theorem arows10111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10111 = true := by
  rw [show D2M8K2.u10111 = KTree.node D2M8K2.t10118 (nat_lit 21559033) (nat_lit 1172219293) (nat_lit 0) D2M8K2.t10119 from rfl, allE_node, rows10118, irow10111, rows10119]
  all_goals rfl

theorem atot10111 : totK PD2M8K2 D2M8K2.u10111 = [0, 0, 337099032283, 927806344340, 499078992619, 37555893550, 1509187004, 0] := by
  rw [show D2M8K2.u10111 = KTree.node D2M8K2.t10118 (nat_lit 21559033) (nat_lit 1172219293) (nat_lit 0) D2M8K2.t10119 from rfl, totK_node, tot10118, tot10119]
  decide +kernel

theorem arows10114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10114 = true := by
  rw [show D2M8K2.u10114 = KTree.node D2M8K2.t10120 (nat_lit 21560836) (nat_lit 2927435482) (nat_lit 0) D2M8K2.t10121 from rfl, allE_node, rows10120, irow10114, rows10121]
  all_goals rfl

theorem atot10114 : totK PD2M8K2 D2M8K2.u10114 = [0, 0, 118732263792, 664521899845, 787001037203, 156453949751, 4720618446, 0] := by
  rw [show D2M8K2.u10114 = KTree.node D2M8K2.t10120 (nat_lit 21560836) (nat_lit 2927435482) (nat_lit 0) D2M8K2.t10121 from rfl, totK_node, tot10120, tot10121]
  decide +kernel

theorem arows10115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10115 = true := by
  rw [show D2M8K2.u10115 = KTree.node D2M8K2.t10122 (nat_lit 21562698) (nat_lit 3229329029) (nat_lit 0) D2M8K2.t10123 from rfl, allE_node, rows10122, irow10115, rows10123]
  all_goals rfl

theorem atot10115 : totK PD2M8K2 D2M8K2.u10115 = [0, 0, 366678412861, 934658852009, 489444120286, 33179173389, 0, 0] := by
  rw [show D2M8K2.u10115 = KTree.node D2M8K2.t10122 (nat_lit 21562698) (nat_lit 3229329029) (nat_lit 0) D2M8K2.t10123 from rfl, totK_node, tot10122, tot10123]
  decide +kernel

theorem arows10117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10117 = true := by
  rw [show D2M8K2.u10117 = KTree.node D2M8K2.t10124 (nat_lit 21566316) (nat_lit 3573901458) (nat_lit 0) D2M8K2.t10125 from rfl, allE_node, rows10124, irow10117, rows10125]
  all_goals rfl

theorem atot10117 : totK PD2M8K2 D2M8K2.u10117 = [0, 323601998422, 859207797920, 478855758754, 106673447658, 12073505261, 0, 0] := by
  rw [show D2M8K2.u10117 = KTree.node D2M8K2.t10124 (nat_lit 21566316) (nat_lit 3573901458) (nat_lit 0) D2M8K2.t10125 from rfl, totK_node, tot10124, tot10125]
  decide +kernel

theorem arows10118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10118 = true := by
  rw [show D2M8K2.u10118 = KTree.node D2M8K2.t10126 (nat_lit 21568434) (nat_lit 3374156220) (nat_lit 0) D2M8K2.t10127 from rfl, allE_node, rows10126, irow10118, rows10127]
  all_goals rfl

theorem atot10118 : totK PD2M8K2 D2M8K2.u10118 = [0, 179148547845, 723489873049, 779832416785, 132944861798, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10118 = KTree.node D2M8K2.t10126 (nat_lit 21568434) (nat_lit 3374156220) (nat_lit 0) D2M8K2.t10127 from rfl, totK_node, tot10126, tot10127]
  decide +kernel

theorem arows10122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10122 = true := by
  rw [show D2M8K2.u10122 = KTree.node D2M8K2.t10128 (nat_lit 21570367) (nat_lit 2289612788) (nat_lit 0) D2M8K2.t10129 from rfl, allE_node, rows10128, irow10122, rows10129]
  all_goals rfl

theorem atot10122 : totK PD2M8K2 D2M8K2.u10122 = [0, 249420483215, 763556678957, 600000156440, 189368990479, 21396654552, 0, 0] := by
  rw [show D2M8K2.u10122 = KTree.node D2M8K2.t10128 (nat_lit 21570367) (nat_lit 2289612788) (nat_lit 0) D2M8K2.t10129 from rfl, totK_node, tot10128, tot10129]
  decide +kernel

theorem arows10123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10123 = true := by
  rw [show D2M8K2.u10123 = KTree.node D2M8K2.t10130 (nat_lit 21571828) (nat_lit 3986255077) (nat_lit 0) D2M8K2.t10131 from rfl, allE_node, rows10130, irow10123, rows10131]
  all_goals rfl

theorem atot10123 : totK PD2M8K2 D2M8K2.u10123 = [0, 63557947097, 446068977534, 876853282422, 391760386568, 16205053670, 0, 0] := by
  rw [show D2M8K2.u10123 = KTree.node D2M8K2.t10130 (nat_lit 21571828) (nat_lit 3986255077) (nat_lit 0) D2M8K2.t10131 from rfl, totK_node, tot10130, tot10131]
  decide +kernel

theorem arows10125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10125 = true := by
  rw [show D2M8K2.u10125 = KTree.node D2M8K2.t10132 (nat_lit 21573134) (nat_lit 3067749570) (nat_lit 0) D2M8K2.t10133 from rfl, allE_node, rows10132, irow10125, rows10133]
  all_goals rfl

theorem atot10125 : totK PD2M8K2 D2M8K2.u10125 = [0, 319808236764, 902236865083, 544855006501, 48793321851, 0, 0, 0] := by
  rw [show D2M8K2.u10125 = KTree.node D2M8K2.t10132 (nat_lit 21573134) (nat_lit 3067749570) (nat_lit 0) D2M8K2.t10133 from rfl, totK_node, tot10132, tot10133]
  decide +kernel

theorem arows10126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10126 = true := by
  rw [show D2M8K2.u10126 = KTree.node D2M8K2.t10134 (nat_lit 21575317) (nat_lit 1029684857) (nat_lit 0) D2M8K2.t10135 from rfl, allE_node, rows10134, irow10126, rows10135]
  all_goals rfl

theorem atot10126 : totK PD2M8K2 D2M8K2.u10126 = [0, 149123110795, 626175445332, 784698349997, 223911856873, 11885407614, 0, 0] := by
  rw [show D2M8K2.u10126 = KTree.node D2M8K2.t10134 (nat_lit 21575317) (nat_lit 1029684857) (nat_lit 0) D2M8K2.t10135 from rfl, totK_node, tot10134, tot10135]
  decide +kernel

theorem arows10129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10129 = true := by
  rw [show D2M8K2.u10129 = KTree.node D2M8K2.t10136 (nat_lit 21577028) (nat_lit 3391518120) (nat_lit 0) D2M8K2.t10137 from rfl, allE_node, rows10136, irow10129, rows10137]
  all_goals rfl

theorem atot10129 : totK PD2M8K2 D2M8K2.u10129 = [0, 266513365864, 847719717591, 614077837684, 82827146894, 1198073392, 0, 0] := by
  rw [show D2M8K2.u10129 = KTree.node D2M8K2.t10136 (nat_lit 21577028) (nat_lit 3391518120) (nat_lit 0) D2M8K2.t10137 from rfl, totK_node, tot10136, tot10137]
  decide +kernel

theorem arows10130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10130 = true := by
  rw [show D2M8K2.u10130 = KTree.node D2M8K2.t10138 (nat_lit 21578752) (nat_lit 3392588987) (nat_lit 0) D2M8K2.t10139 from rfl, allE_node, rows10138, irow10130, rows10139]
  all_goals rfl

theorem atot10130 : totK PD2M8K2 D2M8K2.u10130 = [0, 103462568247, 572273356153, 829746240932, 263449933402, 12052611869, 0, 0] := by
  rw [show D2M8K2.u10130 = KTree.node D2M8K2.t10138 (nat_lit 21578752) (nat_lit 3392588987) (nat_lit 0) D2M8K2.t10139 from rfl, totK_node, tot10138, tot10139]
  decide +kernel

theorem arows10132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10132 = true := by
  rw [show D2M8K2.u10132 = KTree.node D2M8K2.t10140 (nat_lit 21580154) (nat_lit 4211893860) (nat_lit 0) D2M8K2.t10141 from rfl, allE_node, rows10140, irow10132, rows10141]
  all_goals rfl

theorem atot10132 : totK PD2M8K2 D2M8K2.u10132 = [0, 328735689347, 911157745866, 538273269273, 45474354174, 0, 0, 0] := by
  rw [show D2M8K2.u10132 = KTree.node D2M8K2.t10140 (nat_lit 21580154) (nat_lit 4211893860) (nat_lit 0) D2M8K2.t10141 from rfl, totK_node, tot10140, tot10141]
  decide +kernel

theorem arows10133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10133 = true := by
  rw [show D2M8K2.u10133 = KTree.node D2M8K2.t10142 (nat_lit 21581959) (nat_lit 2391364211) (nat_lit 0) D2M8K2.t10143 from rfl, allE_node, rows10142, irow10133, rows10143]
  all_goals rfl

theorem atot10133 : totK PD2M8K2 D2M8K2.u10133 = [0, 0, 498389453652, 1008089387441, 275537431308, 6350335412, 0, 0] := by
  rw [show D2M8K2.u10133 = KTree.node D2M8K2.t10142 (nat_lit 21581959) (nat_lit 2391364211) (nat_lit 0) D2M8K2.t10143 from rfl, totK_node, tot10142, tot10143]
  decide +kernel

theorem arows10138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10138 = true := by
  rw [show D2M8K2.u10138 = KTree.node D2M8K2.t10144 (nat_lit 21587424) (nat_lit 3577290238) (nat_lit 0) D2M8K2.t10145 from rfl, allE_node, rows10144, irow10138, rows10145]
  all_goals rfl

theorem atot10138 : totK PD2M8K2 D2M8K2.u10138 = [0, 0, 383006404948, 924892850892, 457740296192, 37967220658, 0, 0] := by
  rw [show D2M8K2.u10138 = KTree.node D2M8K2.t10144 (nat_lit 21587424) (nat_lit 3577290238) (nat_lit 0) D2M8K2.t10145 from rfl, totK_node, tot10144, tot10145]
  decide +kernel

theorem arows10139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10139 = true := by
  rw [show D2M8K2.u10139 = KTree.node D2M8K2.t10146 (nat_lit 21590901) (nat_lit 1740482660) (nat_lit 0) D2M8K2.t10147 from rfl, allE_node, rows10146, irow10139, rows10147]
  all_goals rfl

theorem atot10139 : totK PD2M8K2 D2M8K2.u10139 = [0, 0, 363556449741, 951974222463, 452755767807, 25248754586, 0, 0] := by
  rw [show D2M8K2.u10139 = KTree.node D2M8K2.t10146 (nat_lit 21590901) (nat_lit 1740482660) (nat_lit 0) D2M8K2.t10147 from rfl, totK_node, tot10146, tot10147]
  decide +kernel

theorem arows10141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10141 = true := by
  rw [show D2M8K2.u10141 = KTree.node D2M8K2.t10148 (nat_lit 21594283) (nat_lit 1737745039) (nat_lit 0) D2M8K2.t10149 from rfl, allE_node, rows10148, irow10141, rows10149]
  all_goals rfl

theorem atot10141 : totK PD2M8K2 D2M8K2.u10141 = [0, 0, 362706993022, 948536694619, 457383493281, 24782452801, 0, 0] := by
  rw [show D2M8K2.u10141 = KTree.node D2M8K2.t10148 (nat_lit 21594283) (nat_lit 1737745039) (nat_lit 0) D2M8K2.t10149 from rfl, totK_node, tot10148, tot10149]
  decide +kernel

theorem arows10142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10142 = true := by
  rw [show D2M8K2.u10142 = KTree.node D2M8K2.t10150 (nat_lit 21597669) (nat_lit 1488247515) (nat_lit 0) D2M8K2.t10151 from rfl, allE_node, rows10150, irow10142, rows10151]
  all_goals rfl

theorem atot10142 : totK PD2M8K2 D2M8K2.u10142 = [0, 0, 390132552384, 947374466972, 458322917967, 26000982174, 0, 0] := by
  rw [show D2M8K2.u10142 = KTree.node D2M8K2.t10150 (nat_lit 21597669) (nat_lit 1488247515) (nat_lit 0) D2M8K2.t10151 from rfl, totK_node, tot10150, tot10151]
  decide +kernel

theorem arows10145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10145 = true := by
  rw [show D2M8K2.u10145 = KTree.node D2M8K2.t10152 (nat_lit 21600690) (nat_lit 2822295892) (nat_lit 0) D2M8K2.t10153 from rfl, allE_node, rows10152, irow10145, rows10153]
  all_goals rfl

theorem atot10145 : totK PD2M8K2 D2M8K2.u10145 = [0, 0, 378461223206, 928281631802, 448843173908, 32547243808, 0, 0] := by
  rw [show D2M8K2.u10145 = KTree.node D2M8K2.t10152 (nat_lit 21600690) (nat_lit 2822295892) (nat_lit 0) D2M8K2.t10153 from rfl, totK_node, tot10152, tot10153]
  decide +kernel

theorem arows10146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10146 = true := by
  rw [show D2M8K2.u10146 = KTree.node D2M8K2.t10154 (nat_lit 21602374) (nat_lit 2438309307) (nat_lit 0) D2M8K2.t10155 from rfl, allE_node, rows10154, irow10146, rows10155]
  all_goals rfl

theorem atot10146 : totK PD2M8K2 D2M8K2.u10146 = [0, 77804430160, 110500103438, 542522541547, 806679029010, 191084932987, 4977114383, 0] := by
  rw [show D2M8K2.u10146 = KTree.node D2M8K2.t10154 (nat_lit 21602374) (nat_lit 2438309307) (nat_lit 0) D2M8K2.t10155 from rfl, totK_node, tot10154, tot10155]
  decide +kernel

theorem arows10148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10148 = true := by
  rw [show D2M8K2.u10148 = KTree.node D2M8K2.t10156 (nat_lit 21608030) (nat_lit 2271264996) (nat_lit 0) D2M8K2.t10157 from rfl, allE_node, rows10156, irow10148, rows10157]
  all_goals rfl

theorem atot10148 : totK PD2M8K2 D2M8K2.u10148 = [0, 249049189214, 830165807239, 628273748551, 95957545054, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10148 = KTree.node D2M8K2.t10156 (nat_lit 21608030) (nat_lit 2271264996) (nat_lit 0) D2M8K2.t10157 from rfl, totK_node, tot10156, tot10157]
  decide +kernel

theorem arows10149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10149 = true := by
  rw [show D2M8K2.u10149 = KTree.node D2M8K2.t10158 (nat_lit 21610838) (nat_lit 4150964372) (nat_lit 0) D2M8K2.t10159 from rfl, allE_node, rows10158, irow10149, rows10159]
  all_goals rfl

theorem atot10149 : totK PD2M8K2 D2M8K2.u10149 = [0, 266888513381, 826164214649, 673101821549, 77582957043, 0, 0, 0] := by
  rw [show D2M8K2.u10149 = KTree.node D2M8K2.t10158 (nat_lit 21610838) (nat_lit 4150964372) (nat_lit 0) D2M8K2.t10159 from rfl, totK_node, tot10158, tot10159]
  decide +kernel

theorem arows10153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10153 = true := by
  rw [show D2M8K2.u10153 = KTree.node D2M8K2.t10160 (nat_lit 21612033) (nat_lit 1427785407) (nat_lit 0) D2M8K2.t10161 from rfl, allE_node, rows10160, irow10153, rows10161]
  all_goals rfl

theorem atot10153 : totK PD2M8K2 D2M8K2.u10153 = [0, 162481956503, 680962516581, 726437226879, 236313305378, 21391863750, 0, 0] := by
  rw [show D2M8K2.u10153 = KTree.node D2M8K2.t10160 (nat_lit 21612033) (nat_lit 1427785407) (nat_lit 0) D2M8K2.t10161 from rfl, totK_node, tot10160, tot10161]
  decide +kernel

theorem arows10154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10154 = true := by
  rw [show D2M8K2.u10154 = KTree.node D2M8K2.t10162 (nat_lit 21613570) (nat_lit 4091617113) (nat_lit 0) D2M8K2.t10163 from rfl, allE_node, rows10162, irow10154, rows10163]
  all_goals rfl

theorem atot10154 : totK PD2M8K2 D2M8K2.u10154 = [0, 152968445628, 548471261451, 750526441872, 338637410529, 16197583040, 0, 0] := by
  rw [show D2M8K2.u10154 = KTree.node D2M8K2.t10162 (nat_lit 21613570) (nat_lit 4091617113) (nat_lit 0) D2M8K2.t10163 from rfl, totK_node, tot10162, tot10163]
  decide +kernel

theorem arows10156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10156 = true := by
  rw [show D2M8K2.u10156 = KTree.node D2M8K2.t10164 (nat_lit 21615216) (nat_lit 2679486683) (nat_lit 0) D2M8K2.t10165 from rfl, allE_node, rows10164, irow10156, rows10165]
  all_goals rfl

theorem atot10156 : totK PD2M8K2 D2M8K2.u10156 = [0, 232413391090, 801622799051, 686644473656, 104996532873, 1164319620, 0, 0] := by
  rw [show D2M8K2.u10156 = KTree.node D2M8K2.t10164 (nat_lit 21615216) (nat_lit 2679486683) (nat_lit 0) D2M8K2.t10165 from rfl, totK_node, tot10164, tot10165]
  decide +kernel

theorem arows10157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10157 = true := by
  rw [show D2M8K2.u10157 = KTree.node D2M8K2.t10166 (nat_lit 21617042) (nat_lit 4024897615) (nat_lit 0) D2M8K2.t10167 from rfl, allE_node, rows10166, irow10157, rows10167]
  all_goals rfl

theorem atot10157 : totK PD2M8K2 D2M8K2.u10157 = [0, 167315818089, 669531558833, 761515326352, 203300296982, 8316300015, 0, 0] := by
  rw [show D2M8K2.u10157 = KTree.node D2M8K2.t10166 (nat_lit 21617042) (nat_lit 4024897615) (nat_lit 0) D2M8K2.t10167 from rfl, totK_node, tot10166, tot10167]
  decide +kernel

theorem arows10160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10160 = true := by
  rw [show D2M8K2.u10160 = KTree.node D2M8K2.t10168 (nat_lit 21618742) (nat_lit 3561620279) (nat_lit 0) D2M8K2.t10169 from rfl, allE_node, rows10168, irow10160, rows10169]
  all_goals rfl

theorem atot10160 : totK PD2M8K2 D2M8K2.u10160 = [0, 249647295150, 793928714465, 667287078414, 108040137349, 1198073392, 0, 0] := by
  rw [show D2M8K2.u10160 = KTree.node D2M8K2.t10168 (nat_lit 21618742) (nat_lit 3561620279) (nat_lit 0) D2M8K2.t10169 from rfl, totK_node, tot10168, tot10169]
  decide +kernel

theorem arows10161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10161 = true := by
  rw [show D2M8K2.u10161 = KTree.node D2M8K2.t10170 (nat_lit 21620461) (nat_lit 1340417973) (nat_lit 0) D2M8K2.t10171 from rfl, allE_node, rows10170, irow10161, rows10171]
  all_goals rfl

theorem atot10161 : totK PD2M8K2 D2M8K2.u10161 = [0, 172675080252, 662984485064, 741217080942, 224039651669, 12010829577, 0, 0] := by
  rw [show D2M8K2.u10161 = KTree.node D2M8K2.t10170 (nat_lit 21620461) (nat_lit 1340417973) (nat_lit 0) D2M8K2.t10171 from rfl, totK_node, tot10170, tot10171]
  decide +kernel

theorem arows10163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10163 = true := by
  rw [show D2M8K2.u10163 = KTree.node D2M8K2.t10172 (nat_lit 21625228) (nat_lit 3162958784) (nat_lit 0) D2M8K2.t10173 from rfl, allE_node, rows10172, irow10163, rows10173]
  all_goals rfl

theorem atot10163 : totK PD2M8K2 D2M8K2.u10163 = [0, 268093655417, 828631788715, 632060888297, 82873057343, 1268739303, 0, 0] := by
  rw [show D2M8K2.u10163 = KTree.node D2M8K2.t10172 (nat_lit 21625228) (nat_lit 3162958784) (nat_lit 0) D2M8K2.t10173 from rfl, totK_node, tot10172, tot10173]
  decide +kernel

theorem arows10164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10164 = true := by
  rw [show D2M8K2.u10164 = KTree.node D2M8K2.t10174 (nat_lit 21626886) (nat_lit 3845860046) (nat_lit 0) D2M8K2.t10175 from rfl, allE_node, rows10174, irow10164, rows10175]
  all_goals rfl

theorem atot10164 : totK PD2M8K2 D2M8K2.u10164 = [0, 0, 426777460925, 958178427095, 372274728908, 20780039840, 0, 0] := by
  rw [show D2M8K2.u10164 = KTree.node D2M8K2.t10174 (nat_lit 21626886) (nat_lit 3845860046) (nat_lit 0) D2M8K2.t10175 from rfl, totK_node, tot10174, tot10175]
  decide +kernel

theorem arows10170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10170 = true := by
  rw [show D2M8K2.u10170 = KTree.node D2M8K2.t10176 (nat_lit 21628778) (nat_lit 3701565113) (nat_lit 0) D2M8K2.t10177 from rfl, allE_node, rows10176, irow10170, rows10177]
  all_goals rfl

theorem atot10170 : totK PD2M8K2 D2M8K2.u10170 = [0, 0, 254957471908, 838377417155, 612635483440, 80989937578, 1310285577, 0] := by
  rw [show D2M8K2.u10170 = KTree.node D2M8K2.t10176 (nat_lit 21628778) (nat_lit 3701565113) (nat_lit 0) D2M8K2.t10177 from rfl, totK_node, tot10176, tot10177]
  decide +kernel

theorem arows10171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10171 = true := by
  rw [show D2M8K2.u10171 = KTree.node D2M8K2.t10178 (nat_lit 21631587) (nat_lit 3693876886) (nat_lit 0) D2M8K2.t10179 from rfl, allE_node, rows10178, irow10171, rows10179]
  all_goals rfl

theorem atot10171 : totK PD2M8K2 D2M8K2.u10171 = [0, 0, 265825288182, 833732715239, 661171731458, 67607042663, 0, 0] := by
  rw [show D2M8K2.u10171 = KTree.node D2M8K2.t10178 (nat_lit 21631587) (nat_lit 3693876886) (nat_lit 0) D2M8K2.t10179 from rfl, totK_node, tot10178, tot10179]
  decide +kernel

theorem arows10173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10173 = true := by
  rw [show D2M8K2.u10173 = KTree.node D2M8K2.t10180 (nat_lit 21632824) (nat_lit 3359797656) (nat_lit 0) D2M8K2.t10181 from rfl, allE_node, rows10180, irow10173, rows10181]
  all_goals rfl

theorem atot10173 : totK PD2M8K2 D2M8K2.u10173 = [0, 0, 361417733041, 925908434017, 510366220829, 41088490608, 0, 0] := by
  rw [show D2M8K2.u10173 = KTree.node D2M8K2.t10180 (nat_lit 21632824) (nat_lit 3359797656) (nat_lit 0) D2M8K2.t10181 from rfl, totK_node, tot10180, tot10181]
  decide +kernel

theorem arows10174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10174 = true := by
  rw [show D2M8K2.u10174 = KTree.node D2M8K2.t10182 (nat_lit 21636195) (nat_lit 3481550644) (nat_lit 0) D2M8K2.t10183 from rfl, allE_node, rows10182, irow10174, rows10183]
  all_goals rfl

theorem atot10174 : totK PD2M8K2 D2M8K2.u10174 = [0, 0, 184732175927, 798538452172, 713558290545, 99441903165, 1435164049, 0] := by
  rw [show D2M8K2.u10174 = KTree.node D2M8K2.t10182 (nat_lit 21636195) (nat_lit 3481550644) (nat_lit 0) D2M8K2.t10183 from rfl, totK_node, tot10182, tot10183]
  decide +kernel

theorem arows10177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10177 = true := by
  rw [show D2M8K2.u10177 = KTree.node D2M8K2.t10184 (nat_lit 21638481) (nat_lit 1712485676) (nat_lit 0) D2M8K2.t10185 from rfl, allE_node, rows10184, irow10177, rows10185]
  all_goals rfl

theorem atot10177 : totK PD2M8K2 D2M8K2.u10177 = [0, 0, 326444115583, 890951959089, 549101139183, 51897379336, 0, 0] := by
  rw [show D2M8K2.u10177 = KTree.node D2M8K2.t10184 (nat_lit 21638481) (nat_lit 1712485676) (nat_lit 0) D2M8K2.t10185 from rfl, totK_node, tot10184, tot10185]
  decide +kernel

theorem arows10178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10178 = true := by
  rw [show D2M8K2.u10178 = KTree.node D2M8K2.t10186 (nat_lit 21640064) (nat_lit 3502266183) (nat_lit 0) D2M8K2.t10187 from rfl, allE_node, rows10186, irow10178, rows10187]
  all_goals rfl

theorem atot10178 : totK PD2M8K2 D2M8K2.u10178 = [0, 0, 89188854363, 656289351625, 840051028503, 175100670636, 4931404646, 0] := by
  rw [show D2M8K2.u10178 = KTree.node D2M8K2.t10186 (nat_lit 21640064) (nat_lit 3502266183) (nat_lit 0) D2M8K2.t10187 from rfl, totK_node, tot10186, tot10187]
  decide +kernel

theorem arows10180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10180 = true := by
  rw [show D2M8K2.u10180 = KTree.node D2M8K2.t10188 (nat_lit 21645505) (nat_lit 1552153127) (nat_lit 0) D2M8K2.t10189 from rfl, allE_node, rows10188, irow10180, rows10189]
  all_goals rfl

theorem atot10180 : totK PD2M8K2 D2M8K2.u10180 = [0, 0, 367555063899, 926738791265, 489741291027, 38872771530, 0, 0] := by
  rw [show D2M8K2.u10180 = KTree.node D2M8K2.t10188 (nat_lit 21645505) (nat_lit 1552153127) (nat_lit 0) D2M8K2.t10189 from rfl, totK_node, tot10188, tot10189]
  decide +kernel

theorem arows10181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10181 = true := by
  rw [show D2M8K2.u10181 = KTree.node D2M8K2.t10190 (nat_lit 21647024) (nat_lit 3201296282) (nat_lit 0) D2M8K2.t10191 from rfl, allE_node, rows10190, irow10181, rows10191]
  all_goals rfl

theorem atot10181 : totK PD2M8K2 D2M8K2.u10181 = [0, 0, 67793698003, 570841697737, 885731353180, 234995185790, 6190766941, 0] := by
  rw [show D2M8K2.u10181 = KTree.node D2M8K2.t10190 (nat_lit 21647024) (nat_lit 3201296282) (nat_lit 0) D2M8K2.t10191 from rfl, totK_node, tot10190, tot10191]
  decide +kernel

theorem arows10185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10185 = true := by
  rw [show D2M8K2.u10185 = KTree.node D2M8K2.t10192 (nat_lit 22395506) (nat_lit 2626047623) (nat_lit 0) D2M8K2.t10193 from rfl, allE_node, rows10192, irow10185, rows10193]
  all_goals rfl

theorem atot10185 : totK PD2M8K2 D2M8K2.u10185 = [0, 310843758421, 734640504326, 389244792507, 216871553681, 127485466193, 11893557120, 0] := by
  rw [show D2M8K2.u10185 = KTree.node D2M8K2.t10192 (nat_lit 22395506) (nat_lit 2626047623) (nat_lit 0) D2M8K2.t10193 from rfl, totK_node, tot10192, tot10193]
  decide +kernel

theorem arows10186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10186 = true := by
  rw [show D2M8K2.u10186 = KTree.node D2M8K2.t10194 (nat_lit 22396710) (nat_lit 3718282347) (nat_lit 0) D2M8K2.t10195 from rfl, allE_node, rows10194, irow10186, rows10195]
  all_goals rfl

theorem atot10186 : totK PD2M8K2 D2M8K2.u10186 = [0, 124655673597, 714025021159, 820844433185, 138369777052, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10186 = KTree.node D2M8K2.t10194 (nat_lit 22396710) (nat_lit 3718282347) (nat_lit 0) D2M8K2.t10195 from rfl, totK_node, tot10194, tot10195]
  decide +kernel

theorem arows10188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10188 = true := by
  rw [show D2M8K2.u10188 = KTree.node D2M8K2.t10196 (nat_lit 22402571) (nat_lit 2420632493) (nat_lit 0) D2M8K2.t10197 from rfl, allE_node, rows10196, irow10188, rows10197]
  all_goals rfl

theorem atot10188 : totK PD2M8K2 D2M8K2.u10188 = [0, 321768215369, 923386793809, 514693144467, 35761348239, 0, 0, 0] := by
  rw [show D2M8K2.u10188 = KTree.node D2M8K2.t10196 (nat_lit 22402571) (nat_lit 2420632493) (nat_lit 0) D2M8K2.t10197 from rfl, totK_node, tot10196, tot10197]
  decide +kernel

theorem arows10189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10189 = true := by
  rw [show D2M8K2.u10189 = KTree.node D2M8K2.t10198 (nat_lit 22404960) (nat_lit 3688938077) (nat_lit 0) D2M8K2.t10199 from rfl, allE_node, rows10198, irow10189, rows10199]
  all_goals rfl

theorem atot10189 : totK PD2M8K2 D2M8K2.u10189 = [0, 160867177514, 669821080253, 774240869092, 171753514113, 4626333750, 0, 0] := by
  rw [show D2M8K2.u10189 = KTree.node D2M8K2.t10198 (nat_lit 22404960) (nat_lit 3688938077) (nat_lit 0) D2M8K2.t10199 from rfl, totK_node, tot10198, tot10199]
  decide +kernel

theorem arows10192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10192 = true := by
  rw [show D2M8K2.u10192 = KTree.node D2M8K2.t10200 (nat_lit 22406596) (nat_lit 3475887134) (nat_lit 0) D2M8K2.t10201 from rfl, allE_node, rows10200, irow10192, rows10201]
  all_goals rfl

theorem atot10192 : totK PD2M8K2 D2M8K2.u10192 = [0, 265439404366, 804813376895, 633072144146, 93379835742, 1198073392, 0, 0] := by
  rw [show D2M8K2.u10192 = KTree.node D2M8K2.t10200 (nat_lit 22406596) (nat_lit 3475887134) (nat_lit 0) D2M8K2.t10201 from rfl, totK_node, tot10200, tot10201]
  decide +kernel

theorem arows10193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10193 = true := by
  rw [show D2M8K2.u10193 = KTree.node D2M8K2.t10202 (nat_lit 22408272) (nat_lit 3591818266) (nat_lit 0) D2M8K2.t10203 from rfl, allE_node, rows10202, irow10193, rows10203]
  all_goals rfl

theorem atot10193 : totK PD2M8K2 D2M8K2.u10193 = [0, 126166914220, 608034486413, 799324788253, 243917198118, 12052611869, 0, 0] := by
  rw [show D2M8K2.u10193 = KTree.node D2M8K2.t10202 (nat_lit 22408272) (nat_lit 3591818266) (nat_lit 0) D2M8K2.t10203 from rfl, totK_node, tot10202, tot10203]
  decide +kernel

theorem arows10195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10195 = true := by
  rw [show D2M8K2.u10195 = KTree.node D2M8K2.t10204 (nat_lit 22409702) (nat_lit 3227362511) (nat_lit 0) D2M8K2.t10205 from rfl, allE_node, rows10204, irow10195, rows10205]
  all_goals rfl

theorem atot10195 : totK PD2M8K2 D2M8K2.u10195 = [0, 282402266066, 848009103009, 576374196853, 65828808022, 1096505104, 0, 0] := by
  rw [show D2M8K2.u10195 = KTree.node D2M8K2.t10204 (nat_lit 22409702) (nat_lit 3227362511) (nat_lit 0) D2M8K2.t10205 from rfl, totK_node, tot10204, tot10205]
  decide +kernel

theorem arows10196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10196 = true := by
  rw [show D2M8K2.u10196 = KTree.node D2M8K2.t10206 (nat_lit 22411668) (nat_lit 3010402658) (nat_lit 0) D2M8K2.t10207 from rfl, allE_node, rows10206, irow10196, rows10207]
  all_goals rfl

theorem atot10196 : totK PD2M8K2 D2M8K2.u10196 = [0, 157174987332, 681782436009, 784627295333, 173783708886, 3884009855, 0, 0] := by
  rw [show D2M8K2.u10196 = KTree.node D2M8K2.t10206 (nat_lit 22411668) (nat_lit 3010402658) (nat_lit 0) D2M8K2.t10207 from rfl, totK_node, tot10206, tot10207]
  decide +kernel

theorem arows10201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10201 = true := by
  rw [show D2M8K2.u10201 = KTree.node D2M8K2.t10208 (nat_lit 22413276) (nat_lit 2753270071) (nat_lit 0) D2M8K2.t10209 from rfl, allE_node, rows10208, irow10201, rows10209]
  all_goals rfl

theorem atot10201 : totK PD2M8K2 D2M8K2.u10201 = [0, 256489885996, 780362986421, 651850581717, 103182330667, 1268739303, 0, 0] := by
  rw [show D2M8K2.u10201 = KTree.node D2M8K2.t10208 (nat_lit 22413276) (nat_lit 2753270071) (nat_lit 0) D2M8K2.t10209 from rfl, totK_node, tot10208, tot10209]
  decide +kernel

theorem arows10202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10202 = true := by
  rw [show D2M8K2.u10202 = KTree.node D2M8K2.t10210 (nat_lit 22414987) (nat_lit 1629704411) (nat_lit 0) D2M8K2.t10211 from rfl, allE_node, rows10210, irow10202, rows10211]
  all_goals rfl

theorem atot10202 : totK PD2M8K2 D2M8K2.u10202 = [0, 0, 416147312252, 964284206103, 380523573398, 17670632056, 0, 0] := by
  rw [show D2M8K2.u10202 = KTree.node D2M8K2.t10210 (nat_lit 22414987) (nat_lit 1629704411) (nat_lit 0) D2M8K2.t10211 from rfl, totK_node, tot10210, tot10211]
  decide +kernel

theorem arows10204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10204 = true := by
  rw [show D2M8K2.u10204 = KTree.node D2M8K2.t10212 (nat_lit 22416794) (nat_lit 3202467206) (nat_lit 0) D2M8K2.t10213 from rfl, allE_node, rows10212, irow10204, rows10213]
  all_goals rfl

theorem atot10204 : totK PD2M8K2 D2M8K2.u10204 = [0, 0, 342103787455, 914951919796, 458612805167, 29810720894, 0, 0] := by
  rw [show D2M8K2.u10204 = KTree.node D2M8K2.t10212 (nat_lit 22416794) (nat_lit 3202467206) (nat_lit 0) D2M8K2.t10213 from rfl, totK_node, tot10212, tot10213]
  decide +kernel

theorem arows10205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10205 = true := by
  rw [show D2M8K2.u10205 = KTree.node D2M8K2.t10214 (nat_lit 22418594) (nat_lit 3696866828) (nat_lit 0) D2M8K2.t10215 from rfl, allE_node, rows10214, irow10205, rows10215]
  all_goals rfl

theorem atot10205 : totK PD2M8K2 D2M8K2.u10205 = [0, 0, 157887881646, 740022313121, 715188306388, 115317567436, 1369150432, 0] := by
  rw [show D2M8K2.u10205 = KTree.node D2M8K2.t10214 (nat_lit 22418594) (nat_lit 3696866828) (nat_lit 0) D2M8K2.t10215 from rfl, totK_node, tot10214, tot10215]
  decide +kernel

theorem arows10208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10208 = true := by
  rw [show D2M8K2.u10208 = KTree.node D2M8K2.t10216 (nat_lit 22426032) (nat_lit 3613646958) (nat_lit 0) D2M8K2.t10217 from rfl, allE_node, rows10216, irow10208, rows10217]
  all_goals rfl

theorem atot10208 : totK PD2M8K2 D2M8K2.u10208 = [0, 0, 396892982514, 975973521037, 400596437442, 13642508798, 0, 0] := by
  rw [show D2M8K2.u10208 = KTree.node D2M8K2.t10216 (nat_lit 22426032) (nat_lit 3613646958) (nat_lit 0) D2M8K2.t10217 from rfl, totK_node, tot10216, tot10217]
  decide +kernel

theorem arows10209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10209 = true := by
  rw [show D2M8K2.u10209 = KTree.node D2M8K2.t10218 (nat_lit 22427563) (nat_lit 1614994545) (nat_lit 0) D2M8K2.t10219 from rfl, allE_node, rows10218, irow10209, rows10219]
  all_goals rfl

theorem atot10209 : totK PD2M8K2 D2M8K2.u10209 = [0, 0, 342607220121, 951429905038, 459142595825, 22498016149, 0, 0] := by
  rw [show D2M8K2.u10209 = KTree.node D2M8K2.t10218 (nat_lit 22427563) (nat_lit 1614994545) (nat_lit 0) D2M8K2.t10219 from rfl, totK_node, tot10218, tot10219]
  decide +kernel

theorem arows10211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10211 = true := by
  rw [show D2M8K2.u10211 = KTree.node D2M8K2.t10220 (nat_lit 22430633) (nat_lit 1729360717) (nat_lit 0) D2M8K2.t10221 from rfl, allE_node, rows10220, irow10211, rows10221]
  all_goals rfl

theorem atot10211 : totK PD2M8K2 D2M8K2.u10211 = [0, 0, 405620668990, 948798411112, 390091618707, 18779930290, 0, 0] := by
  rw [show D2M8K2.u10211 = KTree.node D2M8K2.t10220 (nat_lit 22430633) (nat_lit 1729360717) (nat_lit 0) D2M8K2.t10221 from rfl, totK_node, tot10220, tot10221]
  decide +kernel

theorem arows10212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10212 = true := by
  rw [show D2M8K2.u10212 = KTree.node D2M8K2.t10222 (nat_lit 22433989) (nat_lit 1130674497) (nat_lit 0) D2M8K2.t10223 from rfl, allE_node, rows10222, irow10212, rows10223]
  all_goals rfl

theorem atot10212 : totK PD2M8K2 D2M8K2.u10212 = [0, 94308289763, 448973569016, 829863270060, 417969229244, 22135095123, 0, 0] := by
  rw [show D2M8K2.u10212 = KTree.node D2M8K2.t10222 (nat_lit 22433989) (nat_lit 1130674497) (nat_lit 0) D2M8K2.t10223 from rfl, totK_node, tot10222, tot10223]
  decide +kernel

theorem arows10216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10216 = true := by
  rw [show D2M8K2.u10216 = KTree.node D2M8K2.t10224 (nat_lit 22440906) (nat_lit 3720273817) (nat_lit 0) D2M8K2.t10225 from rfl, allE_node, rows10224, irow10216, rows10225]
  all_goals rfl

theorem atot10216 : totK PD2M8K2 D2M8K2.u10216 = [0, 349794488288, 933020257182, 515722046040, 33562374070, 0, 0, 0] := by
  rw [show D2M8K2.u10216 = KTree.node D2M8K2.t10224 (nat_lit 22440906) (nat_lit 3720273817) (nat_lit 0) D2M8K2.t10225 from rfl, totK_node, tot10224, tot10225]
  decide +kernel

theorem arows10217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10217 = true := by
  rw [show D2M8K2.u10217 = KTree.node D2M8K2.t10226 (nat_lit 22442357) (nat_lit 2303719456) (nat_lit 0) D2M8K2.t10227 from rfl, allE_node, rows10226, irow10217, rows10227]
  all_goals rfl

theorem atot10217 : totK PD2M8K2 D2M8K2.u10217 = [0, 0, 390983822535, 947256793663, 449820768022, 30804453458, 0, 0] := by
  rw [show D2M8K2.u10217 = KTree.node D2M8K2.t10226 (nat_lit 22442357) (nat_lit 2303719456) (nat_lit 0) D2M8K2.t10227 from rfl, totK_node, tot10226, tot10227]
  decide +kernel

theorem arows10219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10219 = true := by
  rw [show D2M8K2.u10219 = KTree.node D2M8K2.t10228 (nat_lit 22443878) (nat_lit 4137008514) (nat_lit 0) D2M8K2.t10229 from rfl, allE_node, rows10228, irow10219, rows10229]
  all_goals rfl

theorem atot10219 : totK PD2M8K2 D2M8K2.u10219 = [0, 320817940962, 812006659731, 562069806054, 142613509757, 6804944647, 0, 0] := by
  rw [show D2M8K2.u10219 = KTree.node D2M8K2.t10228 (nat_lit 22443878) (nat_lit 4137008514) (nat_lit 0) D2M8K2.t10229 from rfl, totK_node, tot10228, tot10229]
  decide +kernel

theorem arows10220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10220 = true := by
  rw [show D2M8K2.u10220 = KTree.node D2M8K2.t10230 (nat_lit 22446189) (nat_lit 1463555763) (nat_lit 0) D2M8K2.t10231 from rfl, allE_node, rows10230, irow10220, rows10231]
  all_goals rfl

theorem atot10220 : totK PD2M8K2 D2M8K2.u10220 = [0, 103136517889, 653153501010, 850573432416, 202517747638, 6910063497, 0, 0] := by
  rw [show D2M8K2.u10220 = KTree.node D2M8K2.t10230 (nat_lit 22446189) (nat_lit 1463555763) (nat_lit 0) D2M8K2.t10231 from rfl, totK_node, tot10230, tot10231]
  decide +kernel

theorem arows10223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10223 = true := by
  rw [show D2M8K2.u10223 = KTree.node D2M8K2.t10232 (nat_lit 22447888) (nat_lit 2357882951) (nat_lit 0) D2M8K2.t10233 from rfl, allE_node, rows10232, irow10223, rows10233]
  all_goals rfl

theorem atot10223 : totK PD2M8K2 D2M8K2.u10223 = [0, 324977130361, 911063798644, 550687954535, 49194789341, 0, 0, 0] := by
  rw [show D2M8K2.u10223 = KTree.node D2M8K2.t10232 (nat_lit 22447888) (nat_lit 2357882951) (nat_lit 0) D2M8K2.t10233 from rfl, totK_node, tot10232, tot10233]
  decide +kernel

theorem arows10224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10224 = true := by
  rw [show D2M8K2.u10224 = KTree.node D2M8K2.t10234 (nat_lit 22449565) (nat_lit 978375078) (nat_lit 0) D2M8K2.t10235 from rfl, allE_node, rows10234, irow10224, rows10235]
  all_goals rfl

theorem atot10224 : totK PD2M8K2 D2M8K2.u10224 = [0, 66330446293, 510407234522, 891901286397, 297308500551, 13237669976, 0, 0] := by
  rw [show D2M8K2.u10224 = KTree.node D2M8K2.t10234 (nat_lit 22449565) (nat_lit 978375078) (nat_lit 0) D2M8K2.t10235 from rfl, totK_node, tot10234, tot10235]
  decide +kernel

theorem arows10226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10226 = true := by
  rw [show D2M8K2.u10226 = KTree.node D2M8K2.t10236 (nat_lit 22450966) (nat_lit 2401274475) (nat_lit 0) D2M8K2.t10237 from rfl, allE_node, rows10236, irow10226, rows10237]
  all_goals rfl

theorem atot10226 : totK PD2M8K2 D2M8K2.u10226 = [0, 345281192724, 932343409671, 504435628211, 38977432266, 0, 0, 0] := by
  rw [show D2M8K2.u10226 = KTree.node D2M8K2.t10236 (nat_lit 22450966) (nat_lit 2401274475) (nat_lit 0) D2M8K2.t10237 from rfl, totK_node, tot10236, tot10237]
  decide +kernel

theorem arows10227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10227 = true := by
  rw [show D2M8K2.u10227 = KTree.node D2M8K2.t10238 (nat_lit 22452854) (nat_lit 3852983560) (nat_lit 0) D2M8K2.t10239 from rfl, allE_node, rows10238, irow10227, rows10239]
  all_goals rfl

theorem atot10227 : totK PD2M8K2 D2M8K2.u10227 = [0, 98420485883, 623562404444, 879212993523, 196839565747, 4976872846, 0, 0] := by
  rw [show D2M8K2.u10227 = KTree.node D2M8K2.t10238 (nat_lit 22452854) (nat_lit 3852983560) (nat_lit 0) D2M8K2.t10239 from rfl, totK_node, tot10238, tot10239]
  decide +kernel

theorem arows10238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10238 = true := by
  rw [show D2M8K2.u10238 = KTree.node D2M8K2.t10240 (nat_lit 22454541) (nat_lit 1403105862) (nat_lit 0) D2M8K2.t10241 from rfl, allE_node, rows10240, irow10238, rows10241]
  all_goals rfl

theorem atot10238 : totK PD2M8K2 D2M8K2.u10238 = [0, 318671753230, 891940784017, 569196896156, 53079053798, 0, 0, 0] := by
  rw [show D2M8K2.u10238 = KTree.node D2M8K2.t10240 (nat_lit 22454541) (nat_lit 1403105862) (nat_lit 0) D2M8K2.t10241 from rfl, totK_node, tot10240, tot10241]
  decide +kernel

theorem arows10239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10239 = true := by
  rw [show D2M8K2.u10239 = KTree.node D2M8K2.t10242 (nat_lit 22456255) (nat_lit 2357434463) (nat_lit 0) D2M8K2.t10243 from rfl, allE_node, rows10242, irow10239, rows10243]
  all_goals rfl

theorem atot10239 : totK PD2M8K2 D2M8K2.u10239 = [0, 0, 418658262662, 954048287067, 392551169713, 20524233051, 0, 0] := by
  rw [show D2M8K2.u10239 = KTree.node D2M8K2.t10242 (nat_lit 22456255) (nat_lit 2357434463) (nat_lit 0) D2M8K2.t10243 from rfl, totK_node, tot10242, tot10243]
  decide +kernel

theorem arows10241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10241 = true := by
  rw [show D2M8K2.u10241 = KTree.node D2M8K2.t10244 (nat_lit 22461450) (nat_lit 3909295455) (nat_lit 0) D2M8K2.t10245 from rfl, allE_node, rows10244, irow10241, rows10245]
  all_goals rfl

theorem atot10241 : totK PD2M8K2 D2M8K2.u10241 = [0, 0, 366891767729, 943253707135, 496864954240, 36231910962, 0, 0] := by
  rw [show D2M8K2.u10241 = KTree.node D2M8K2.t10244 (nat_lit 22461450) (nat_lit 3909295455) (nat_lit 0) D2M8K2.t10245 from rfl, totK_node, tot10244, tot10245]
  decide +kernel

theorem arows10242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10242 = true := by
  rw [show D2M8K2.u10242 = KTree.node D2M8K2.t10246 (nat_lit 22462899) (nat_lit 3681445855) (nat_lit 0) D2M8K2.t10247 from rfl, allE_node, rows10246, irow10242, rows10247]
  all_goals rfl

theorem atot10242 : totK PD2M8K2 D2M8K2.u10242 = [0, 0, 34473473380, 496870521977, 899544955726, 346337661707, 24064559466, 0] := by
  rw [show D2M8K2.u10242 = KTree.node D2M8K2.t10246 (nat_lit 22462899) (nat_lit 3681445855) (nat_lit 0) D2M8K2.t10247 from rfl, totK_node, tot10246, tot10247]
  decide +kernel

theorem arows10245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10245 = true := by
  rw [show D2M8K2.u10245 = KTree.node D2M8K2.t10248 (nat_lit 22464494) (nat_lit 3866018160) (nat_lit 0) D2M8K2.t10249 from rfl, allE_node, rows10248, irow10245, rows10249]
  all_goals rfl

theorem atot10245 : totK PD2M8K2 D2M8K2.u10245 = [0, 0, 257588056033, 727050846487, 634080934827, 187254782374, 6505774710, 0] := by
  rw [show D2M8K2.u10245 = KTree.node D2M8K2.t10248 (nat_lit 22464494) (nat_lit 3866018160) (nat_lit 0) D2M8K2.t10249 from rfl, totK_node, tot10248, tot10249]
  decide +kernel

theorem arows10246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10246 = true := by
  rw [show D2M8K2.u10246 = KTree.node D2M8K2.t10250 (nat_lit 22466942) (nat_lit 3697042353) (nat_lit 0) D2M8K2.t10251 from rfl, allE_node, rows10250, irow10246, rows10251]
  all_goals rfl

theorem atot10246 : totK PD2M8K2 D2M8K2.u10246 = [0, 0, 197090308537, 787586672233, 732179079881, 99143189498, 1149959346, 0] := by
  rw [show D2M8K2.u10246 = KTree.node D2M8K2.t10250 (nat_lit 22466942) (nat_lit 3697042353) (nat_lit 0) D2M8K2.t10251 from rfl, totK_node, tot10250, tot10251]
  decide +kernel

theorem arows10248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10248 = true := by
  rw [show D2M8K2.u10248 = KTree.node D2M8K2.t10252 (nat_lit 22468664) (nat_lit 3779082584) (nat_lit 0) D2M8K2.t10253 from rfl, allE_node, rows10252, irow10248, rows10253]
  all_goals rfl

theorem atot10248 : totK PD2M8K2 D2M8K2.u10248 = [0, 0, 294749669766, 900204262313, 575728050642, 47640263496, 0, 0] := by
  rw [show D2M8K2.u10248 = KTree.node D2M8K2.t10252 (nat_lit 22468664) (nat_lit 3779082584) (nat_lit 0) D2M8K2.t10253 from rfl, totK_node, tot10252, tot10253]
  decide +kernel

theorem arows10249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10249 = true := by
  rw [show D2M8K2.u10249 = KTree.node D2M8K2.t10254 (nat_lit 22470490) (nat_lit 1060336493) (nat_lit 0) D2M8K2.t10255 from rfl, allE_node, rows10254, irow10249, rows10255]
  all_goals rfl

theorem atot10249 : totK PD2M8K2 D2M8K2.u10249 = [0, 0, 155730778514, 642066904326, 778533866647, 201755247489, 5218872685, 0] := by
  rw [show D2M8K2.u10249 = KTree.node D2M8K2.t10254 (nat_lit 22470490) (nat_lit 1060336493) (nat_lit 0) D2M8K2.t10255 from rfl, totK_node, tot10254, tot10255]
  decide +kernel

theorem arows10253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10253 = true := by
  rw [show D2M8K2.u10253 = KTree.node D2M8K2.t10256 (nat_lit 22471947) (nat_lit 3724991613) (nat_lit 0) D2M8K2.t10257 from rfl, allE_node, rows10256, irow10253, rows10257]
  all_goals rfl

theorem atot10253 : totK PD2M8K2 D2M8K2.u10253 = [0, 0, 254905018120, 862197348063, 626903874280, 57988281287, 0, 0] := by
  rw [show D2M8K2.u10253 = KTree.node D2M8K2.t10256 (nat_lit 22471947) (nat_lit 3724991613) (nat_lit 0) D2M8K2.t10257 from rfl, totK_node, tot10256, tot10257]
  decide +kernel

theorem arows10254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10254 = true := by
  rw [show D2M8K2.u10254 = KTree.node D2M8K2.t10258 (nat_lit 22474368) (nat_lit 3736707029) (nat_lit 0) D2M8K2.t10259 from rfl, allE_node, rows10258, irow10254, rows10259]
  all_goals rfl

theorem atot10254 : totK PD2M8K2 D2M8K2.u10254 = [0, 0, 200342827364, 741331664342, 760363307568, 125232942069, 1415142070, 0] := by
  rw [show D2M8K2.u10254 = KTree.node D2M8K2.t10258 (nat_lit 22474368) (nat_lit 3736707029) (nat_lit 0) D2M8K2.t10259 from rfl, totK_node, tot10258, tot10259]
  decide +kernel

theorem arows10256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10256 = true := by
  rw [show D2M8K2.u10256 = KTree.node D2M8K2.t10260 (nat_lit 22475902) (nat_lit 3922075906) (nat_lit 0) D2M8K2.t10261 from rfl, allE_node, rows10260, irow10256, rows10261]
  all_goals rfl

theorem atot10256 : totK PD2M8K2 D2M8K2.u10256 = [0, 0, 212808207772, 835645340339, 685649153553, 79584991758, 0, 0] := by
  rw [show D2M8K2.u10256 = KTree.node D2M8K2.t10260 (nat_lit 22475902) (nat_lit 3922075906) (nat_lit 0) D2M8K2.t10261 from rfl, totK_node, tot10260, tot10261]
  decide +kernel

theorem arows10257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10257 = true := by
  rw [show D2M8K2.u10257 = KTree.node D2M8K2.t10262 (nat_lit 22519348) (nat_lit 3657562500) (nat_lit 0) D2M8K2.t10263 from rfl, allE_node, rows10262, irow10257, rows10263]
  all_goals rfl

theorem atot10257 : totK PD2M8K2 D2M8K2.u10257 = [0, 241137231530, 512056197858, 363453660001, 459115137137, 183393117114, 6672335165, 0] := by
  rw [show D2M8K2.u10257 = KTree.node D2M8K2.t10262 (nat_lit 22519348) (nat_lit 3657562500) (nat_lit 0) D2M8K2.t10263 from rfl, totK_node, tot10262, tot10263]
  decide +kernel

theorem arows10260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10260 = true := by
  rw [show D2M8K2.u10260 = KTree.node D2M8K2.t10264 (nat_lit 22520890) (nat_lit 3937868485) (nat_lit 0) D2M8K2.t10265 from rfl, allE_node, rows10264, irow10260, rows10265]
  all_goals rfl

theorem atot10260 : totK PD2M8K2 D2M8K2.u10260 = [0, 175688188989, 754547664439, 734564185516, 120458450008, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10260 = KTree.node D2M8K2.t10264 (nat_lit 22520890) (nat_lit 3937868485) (nat_lit 0) D2M8K2.t10265 from rfl, totK_node, tot10264, tot10265]
  decide +kernel

theorem arows10261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10261 = true := by
  rw [show D2M8K2.u10261 = KTree.node D2M8K2.t10266 (nat_lit 22523241) (nat_lit 1772870703) (nat_lit 0) D2M8K2.t10267 from rfl, allE_node, rows10266, irow10261, rows10267]
  all_goals rfl

theorem atot10261 : totK PD2M8K2 D2M8K2.u10261 = [0, 252115962124, 838216442267, 679158371897, 74144270441, 0, 0, 0] := by
  rw [show D2M8K2.u10261 = KTree.node D2M8K2.t10266 (nat_lit 22523241) (nat_lit 1772870703) (nat_lit 0) D2M8K2.t10267 from rfl, totK_node, tot10266, tot10267]
  decide +kernel

theorem arows10263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10263 = true := by
  rw [show D2M8K2.u10263 = KTree.node D2M8K2.t10268 (nat_lit 22524474) (nat_lit 3364367115) (nat_lit 0) D2M8K2.t10269 from rfl, allE_node, rows10268, irow10263, rows10269]
  all_goals rfl

theorem atot10263 : totK PD2M8K2 D2M8K2.u10263 = [0, 174351684497, 653735976296, 699308105856, 269216587321, 23209944845, 0, 0] := by
  rw [show D2M8K2.u10263 = KTree.node D2M8K2.t10268 (nat_lit 22524474) (nat_lit 3364367115) (nat_lit 0) D2M8K2.t10269 from rfl, totK_node, tot10268, tot10269]
  decide +kernel

theorem arows10264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10264 = true := by
  rw [show D2M8K2.u10264 = KTree.node D2M8K2.t10270 (nat_lit 22525994) (nat_lit 4038140179) (nat_lit 0) D2M8K2.t10271 from rfl, allE_node, rows10270, irow10264, rows10271]
  all_goals rfl

theorem atot10264 : totK PD2M8K2 D2M8K2.u10264 = [0, 176600050142, 590252022594, 740137310232, 297245281546, 11941493701, 0, 0] := by
  rw [show D2M8K2.u10264 = KTree.node D2M8K2.t10270 (nat_lit 22525994) (nat_lit 4038140179) (nat_lit 0) D2M8K2.t10271 from rfl, totK_node, tot10270, tot10271]
  decide +kernel

theorem arows10269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10269 = true := by
  rw [show D2M8K2.u10269 = KTree.node D2M8K2.t10272 (nat_lit 22530913) (nat_lit 1487711996) (nat_lit 0) D2M8K2.t10273 from rfl, allE_node, rows10272, irow10269, rows10273]
  all_goals rfl

theorem atot10269 : totK PD2M8K2 D2M8K2.u10269 = [0, 270100032260, 873994806402, 636286447683, 60854157252, 0, 0, 0] := by
  rw [show D2M8K2.u10269 = KTree.node D2M8K2.t10272 (nat_lit 22530913) (nat_lit 1487711996) (nat_lit 0) D2M8K2.t10273 from rfl, totK_node, tot10272, tot10273]
  decide +kernel

theorem arows10270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10270 = true := by
  rw [show D2M8K2.u10270 = KTree.node D2M8K2.t10274 (nat_lit 22532577) (nat_lit 1847973604) (nat_lit 0) D2M8K2.t10275 from rfl, allE_node, rows10274, irow10270, rows10275]
  all_goals rfl

theorem atot10270 : totK PD2M8K2 D2M8K2.u10270 = [0, 84422589187, 531791841758, 866327539220, 290580232080, 13250685261, 0, 0] := by
  rw [show D2M8K2.u10270 = KTree.node D2M8K2.t10274 (nat_lit 22532577) (nat_lit 1847973604) (nat_lit 0) D2M8K2.t10275 from rfl, totK_node, tot10274, tot10275]
  decide +kernel

theorem arows10272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10272 = true := by
  rw [show D2M8K2.u10272 = KTree.node D2M8K2.t10276 (nat_lit 22533988) (nat_lit 2690969518) (nat_lit 0) D2M8K2.t10277 from rfl, allE_node, rows10276, irow10272, rows10277]
  all_goals rfl

theorem atot10272 : totK PD2M8K2 D2M8K2.u10272 = [0, 335103320822, 914922890102, 527232374787, 41932464919, 0, 0, 0] := by
  rw [show D2M8K2.u10272 = KTree.node D2M8K2.t10276 (nat_lit 22533988) (nat_lit 2690969518) (nat_lit 0) D2M8K2.t10277 from rfl, totK_node, tot10276, tot10277]
  decide +kernel

theorem arows10273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10273 = true := by
  rw [show D2M8K2.u10273 = KTree.node D2M8K2.t10278 (nat_lit 22535814) (nat_lit 3878967719) (nat_lit 0) D2M8K2.t10279 from rfl, allE_node, rows10278, irow10273, rows10279]
  all_goals rfl

theorem atot10273 : totK PD2M8K2 D2M8K2.u10273 = [0, 104752565381, 619099246529, 858840139856, 197632000890, 4980514959, 0, 0] := by
  rw [show D2M8K2.u10273 = KTree.node D2M8K2.t10278 (nat_lit 22535814) (nat_lit 3878967719) (nat_lit 0) D2M8K2.t10279 from rfl, totK_node, tot10278, tot10279]
  decide +kernel

theorem arows10276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10276 = true := by
  rw [show D2M8K2.u10276 = KTree.node D2M8K2.t10280 (nat_lit 22537515) (nat_lit 3648144827) (nat_lit 0) D2M8K2.t10281 from rfl, allE_node, rows10280, irow10276, rows10281]
  all_goals rfl

theorem atot10276 : totK PD2M8K2 D2M8K2.u10276 = [0, 319054120400, 898497446536, 567227084668, 51681516494, 0, 0, 0] := by
  rw [show D2M8K2.u10276 = KTree.node D2M8K2.t10280 (nat_lit 22537515) (nat_lit 3648144827) (nat_lit 0) D2M8K2.t10281 from rfl, totK_node, tot10280, tot10281]
  decide +kernel

theorem arows10277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10277 = true := by
  rw [show D2M8K2.u10277 = KTree.node D2M8K2.t10282 (nat_lit 22539194) (nat_lit 4204749349) (nat_lit 0) D2M8K2.t10283 from rfl, allE_node, rows10282, irow10277, rows10283]
  all_goals rfl

theorem atot10277 : totK PD2M8K2 D2M8K2.u10277 = [0, 0, 411847553489, 958107890334, 386301326991, 20066742562, 0, 0] := by
  rw [show D2M8K2.u10277 = KTree.node D2M8K2.t10282 (nat_lit 22539194) (nat_lit 4204749349) (nat_lit 0) D2M8K2.t10283 from rfl, totK_node, tot10282, tot10283]
  decide +kernel

theorem arows10279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10279 = true := by
  rw [show D2M8K2.u10279 = KTree.node D2M8K2.t10284 (nat_lit 22541049) (nat_lit 1733840724) (nat_lit 0) D2M8K2.t10285 from rfl, allE_node, rows10284, irow10279, rows10285]
  all_goals rfl

theorem atot10279 : totK PD2M8K2 D2M8K2.u10279 = [0, 0, 379267968261, 970711064500, 404230394837, 16140727502, 0, 0] := by
  rw [show D2M8K2.u10279 = KTree.node D2M8K2.t10284 (nat_lit 22541049) (nat_lit 1733840724) (nat_lit 0) D2M8K2.t10285 from rfl, totK_node, tot10284, tot10285]
  decide +kernel

theorem arows10280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10280 = true := by
  rw [show D2M8K2.u10280 = KTree.node D2M8K2.t10286 (nat_lit 22542921) (nat_lit 1853830114) (nat_lit 0) D2M8K2.t10287 from rfl, allE_node, rows10286, irow10280, rows10287]
  all_goals rfl

theorem atot10280 : totK PD2M8K2 D2M8K2.u10280 = [0, 0, 93173791751, 688302500055, 853872790759, 128729371296, 1239866073, 0] := by
  rw [show D2M8K2.u10280 = KTree.node D2M8K2.t10286 (nat_lit 22542921) (nat_lit 1853830114) (nat_lit 0) D2M8K2.t10287 from rfl, totK_node, tot10286, tot10287]
  decide +kernel

theorem arows10284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10284 = true := by
  rw [show D2M8K2.u10284 = KTree.node D2M8K2.t10288 (nat_lit 22544712) (nat_lit 3137092029) (nat_lit 0) D2M8K2.t10289 from rfl, allE_node, rows10288, irow10284, rows10289]
  all_goals rfl

theorem atot10284 : totK PD2M8K2 D2M8K2.u10284 = [0, 0, 402530100879, 955740265047, 436455186186, 24875783287, 0, 0] := by
  rw [show D2M8K2.u10284 = KTree.node D2M8K2.t10288 (nat_lit 22544712) (nat_lit 3137092029) (nat_lit 0) D2M8K2.t10289 from rfl, totK_node, tot10288, tot10289]
  decide +kernel

theorem arows10285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10285 = true := by
  rw [show D2M8K2.u10285 = KTree.node D2M8K2.t10290 (nat_lit 22551394) (nat_lit 4123203255) (nat_lit 0) D2M8K2.t10291 from rfl, allE_node, rows10290, irow10285, rows10291]
  all_goals rfl

theorem atot10285 : totK PD2M8K2 D2M8K2.u10285 = [0, 0, 369581502267, 950668242176, 474365021474, 32359824416, 0, 0] := by
  rw [show D2M8K2.u10285 = KTree.node D2M8K2.t10290 (nat_lit 22551394) (nat_lit 4123203255) (nat_lit 0) D2M8K2.t10291 from rfl, totK_node, tot10290, tot10291]
  decide +kernel

theorem arows10287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10287 = true := by
  rw [show D2M8K2.u10287 = KTree.node D2M8K2.t10292 (nat_lit 22553076) (nat_lit 3218112320) (nat_lit 0) D2M8K2.t10293 from rfl, allE_node, rows10292, irow10287, rows10293]
  all_goals rfl

theorem atot10287 : totK PD2M8K2 D2M8K2.u10287 = [0, 0, 0, 505572070055, 944306938895, 279812921148, 13105450397, 0] := by
  rw [show D2M8K2.u10287 = KTree.node D2M8K2.t10292 (nat_lit 22553076) (nat_lit 3218112320) (nat_lit 0) D2M8K2.t10293 from rfl, totK_node, tot10292, tot10293]
  decide +kernel

theorem arows10288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10288 = true := by
  rw [show D2M8K2.u10288 = KTree.node D2M8K2.t10294 (nat_lit 22554462) (nat_lit 3250847812) (nat_lit 0) D2M8K2.t10295 from rfl, allE_node, rows10294, irow10288, rows10295]
  all_goals rfl

theorem atot10288 : totK PD2M8K2 D2M8K2.u10288 = [0, 0, 398307766086, 941286153090, 427666690742, 27067921785, 0, 0] := by
  rw [show D2M8K2.u10288 = KTree.node D2M8K2.t10294 (nat_lit 22554462) (nat_lit 3250847812) (nat_lit 0) D2M8K2.t10295 from rfl, totK_node, tot10294, tot10295]
  decide +kernel

theorem arows10291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10291 = true := by
  rw [show D2M8K2.u10291 = KTree.node D2M8K2.t10296 (nat_lit 22556265) (nat_lit 1900535491) (nat_lit 0) D2M8K2.t10297 from rfl, allE_node, rows10296, irow10291, rows10297]
  all_goals rfl

theorem atot10291 : totK PD2M8K2 D2M8K2.u10291 = [0, 0, 103805003574, 656195628374, 793336246386, 159711959550, 4720618446, 0] := by
  rw [show D2M8K2.u10291 = KTree.node D2M8K2.t10296 (nat_lit 22556265) (nat_lit 1900535491) (nat_lit 0) D2M8K2.t10297 from rfl, totK_node, tot10296, tot10297]
  decide +kernel

theorem arows10292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10292 = true := by
  rw [show D2M8K2.u10292 = KTree.node D2M8K2.t10298 (nat_lit 22558083) (nat_lit 2971908335) (nat_lit 0) D2M8K2.t10299 from rfl, allE_node, rows10298, irow10292, rows10299]
  all_goals rfl

theorem atot10292 : totK PD2M8K2 D2M8K2.u10292 = [0, 0, 337592194433, 923896623887, 518047717963, 35800607630, 0, 0] := by
  rw [show D2M8K2.u10292 = KTree.node D2M8K2.t10298 (nat_lit 22558083) (nat_lit 2971908335) (nat_lit 0) D2M8K2.t10299 from rfl, totK_node, tot10298, tot10299]
  decide +kernel

theorem arows10294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10294 = true := by
  rw [show D2M8K2.u10294 = KTree.node D2M8K2.t10300 (nat_lit 22561645) (nat_lit 1386241413) (nat_lit 0) D2M8K2.t10301 from rfl, allE_node, rows10300, irow10294, rows10301]
  all_goals rfl

theorem atot10294 : totK PD2M8K2 D2M8K2.u10294 = [0, 373524860364, 906945553972, 425939955519, 60177682643, 8677971875, 0, 0] := by
  rw [show D2M8K2.u10294 = KTree.node D2M8K2.t10300 (nat_lit 22561645) (nat_lit 1386241413) (nat_lit 0) D2M8K2.t10301 from rfl, totK_node, tot10300, tot10301]
  decide +kernel

theorem arows10295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10295 = true := by
  rw [show D2M8K2.u10295 = KTree.node D2M8K2.t10302 (nat_lit 22563367) (nat_lit 2391034705) (nat_lit 0) D2M8K2.t10303 from rfl, allE_node, rows10302, irow10295, rows10303]
  all_goals rfl

theorem atot10295 : totK PD2M8K2 D2M8K2.u10295 = [0, 125606933847, 680528319072, 840750534912, 143511132191, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10295 = KTree.node D2M8K2.t10302 (nat_lit 22563367) (nat_lit 2391034705) (nat_lit 0) D2M8K2.t10303 from rfl, totK_node, tot10302, tot10303]
  decide +kernel

theorem arows10301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10301 = true := by
  rw [show D2M8K2.u10301 = KTree.node D2M8K2.t10304 (nat_lit 22565250) (nat_lit 3298849058) (nat_lit 0) D2M8K2.t10305 from rfl, allE_node, rows10304, irow10301, rows10305]
  all_goals rfl

theorem atot10301 : totK PD2M8K2 D2M8K2.u10301 = [0, 324575920315, 906152293485, 547285188614, 45398558913, 0, 0, 0] := by
  rw [show D2M8K2.u10301 = KTree.node D2M8K2.t10304 (nat_lit 22565250) (nat_lit 3298849058) (nat_lit 0) D2M8K2.t10305 from rfl, totK_node, tot10304, tot10305]
  decide +kernel

theorem arows10302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10302 = true := by
  rw [show D2M8K2.u10302 = KTree.node D2M8K2.t10306 (nat_lit 22566795) (nat_lit 3435342992) (nat_lit 0) D2M8K2.t10307 from rfl, allE_node, rows10306, irow10302, rows10307]
  all_goals rfl

theorem atot10302 : totK PD2M8K2 D2M8K2.u10302 = [0, 0, 384158784928, 941463278302, 455455884609, 30547224044, 0, 0] := by
  rw [show D2M8K2.u10302 = KTree.node D2M8K2.t10306 (nat_lit 22566795) (nat_lit 3435342992) (nat_lit 0) D2M8K2.t10307 from rfl, totK_node, tot10306, tot10307]
  decide +kernel

theorem arows10304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10304 = true := by
  rw [show D2M8K2.u10304 = KTree.node D2M8K2.t10308 (nat_lit 22568145) (nat_lit 1752303176) (nat_lit 0) D2M8K2.t10309 from rfl, allE_node, rows10308, irow10304, rows10309]
  all_goals rfl

theorem atot10304 : totK PD2M8K2 D2M8K2.u10304 = [0, 323533095032, 861183565543, 499232236516, 110994855180, 5355925179, 0, 0] := by
  rw [show D2M8K2.u10304 = KTree.node D2M8K2.t10308 (nat_lit 22568145) (nat_lit 1752303176) (nat_lit 0) D2M8K2.t10309 from rfl, totK_node, tot10308, tot10309]
  decide +kernel

theorem arows10305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10305 = true := by
  rw [show D2M8K2.u10305 = KTree.node D2M8K2.t10310 (nat_lit 22570613) (nat_lit 2384613374) (nat_lit 0) D2M8K2.t10311 from rfl, allE_node, rows10310, irow10305, rows10311]
  all_goals rfl

theorem atot10305 : totK PD2M8K2 D2M8K2.u10305 = [0, 173099396876, 666452170529, 762192056748, 168040520507, 4626333750, 0, 0] := by
  rw [show D2M8K2.u10305 = KTree.node D2M8K2.t10310 (nat_lit 22570613) (nat_lit 2384613374) (nat_lit 0) D2M8K2.t10311 from rfl, totK_node, tot10310, tot10311]
  decide +kernel

theorem arows10308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10308 = true := by
  rw [show D2M8K2.u10308 = KTree.node D2M8K2.t10312 (nat_lit 22572385) (nat_lit 1487711996) (nat_lit 0) D2M8K2.t10313 from rfl, allE_node, rows10312, irow10308, rows10313]
  all_goals rfl

theorem atot10308 : totK PD2M8K2 D2M8K2.u10308 = [0, 253428006762, 827434648975, 640965964505, 88705008343, 1198073392, 0, 0] := by
  rw [show D2M8K2.u10308 = KTree.node D2M8K2.t10312 (nat_lit 22572385) (nat_lit 1487711996) (nat_lit 0) D2M8K2.t10313 from rfl, totK_node, tot10312, tot10313]
  decide +kernel

theorem arows10309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10309 = true := by
  rw [show D2M8K2.u10309 = KTree.node D2M8K2.t10314 (nat_lit 22574091) (nat_lit 3612560933) (nat_lit 0) D2M8K2.t10315 from rfl, allE_node, rows10314, irow10309, rows10315]
  all_goals rfl

theorem atot10309 : totK PD2M8K2 D2M8K2.u10309 = [0, 105483684527, 588044410935, 828267005023, 259619229184, 12052611869, 0, 0] := by
  rw [show D2M8K2.u10309 = KTree.node D2M8K2.t10314 (nat_lit 22574091) (nat_lit 3612560933) (nat_lit 0) D2M8K2.t10315 from rfl, totK_node, tot10314, tot10315]
  decide +kernel

theorem arows10311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10311 = true := by
  rw [show D2M8K2.u10311 = KTree.node D2M8K2.t10316 (nat_lit 22575485) (nat_lit 1798411626) (nat_lit 0) D2M8K2.t10317 from rfl, allE_node, rows10316, irow10311, rows10317]
  all_goals rfl

theorem atot10311 : totK PD2M8K2 D2M8K2.u10311 = [0, 332411104527, 903508668676, 536016377688, 48933806979, 0, 0, 0] := by
  rw [show D2M8K2.u10311 = KTree.node D2M8K2.t10316 (nat_lit 22575485) (nat_lit 1798411626) (nat_lit 0) D2M8K2.t10317 from rfl, totK_node, tot10316, tot10317]
  decide +kernel

theorem arows10312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10312 = true := by
  rw [show D2M8K2.u10312 = KTree.node D2M8K2.t10318 (nat_lit 22577289) (nat_lit 1907098634) (nat_lit 0) D2M8K2.t10319 from rfl, allE_node, rows10318, irow10312, rows10319]
  all_goals rfl

theorem atot10312 : totK PD2M8K2 D2M8K2.u10312 = [0, 0, 500727525995, 1011652875341, 278378123423, 6350335412, 0, 0] := by
  rw [show D2M8K2.u10312 = KTree.node D2M8K2.t10318 (nat_lit 22577289) (nat_lit 1907098634) (nat_lit 0) D2M8K2.t10319 from rfl, totK_node, tot10318, tot10319]
  decide +kernel

theorem arows10316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10316 = true := by
  rw [show D2M8K2.u10316 = KTree.node D2M8K2.t10320 (nat_lit 22582715) (nat_lit 1947512094) (nat_lit 0) D2M8K2.t10321 from rfl, allE_node, rows10320, irow10316, rows10321]
  all_goals rfl

theorem atot10316 : totK PD2M8K2 D2M8K2.u10316 = [0, 0, 301126554669, 870323138506, 490845100033, 54066595802, 1138244013, 0] := by
  rw [show D2M8K2.u10316 = KTree.node D2M8K2.t10320 (nat_lit 22582715) (nat_lit 1947512094) (nat_lit 0) D2M8K2.t10321 from rfl, totK_node, tot10320, tot10321]
  decide +kernel

theorem arows10317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10317 = true := by
  rw [show D2M8K2.u10317 = KTree.node D2M8K2.t10322 (nat_lit 22585328) (nat_lit 3731953676) (nat_lit 0) D2M8K2.t10323 from rfl, allE_node, rows10322, irow10317, rows10323]
  all_goals rfl

theorem atot10317 : totK PD2M8K2 D2M8K2.u10317 = [0, 0, 230633770983, 830571344588, 654793733955, 65787444726, 0, 0] := by
  rw [show D2M8K2.u10317 = KTree.node D2M8K2.t10322 (nat_lit 22585328) (nat_lit 3731953676) (nat_lit 0) D2M8K2.t10323 from rfl, totK_node, tot10322, tot10323]
  decide +kernel

theorem arows10319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10319 = true := by
  rw [show D2M8K2.u10319 = KTree.node D2M8K2.t10324 (nat_lit 22586601) (nat_lit 1222665432) (nat_lit 0) D2M8K2.t10325 from rfl, allE_node, rows10324, irow10319, rows10325]
  all_goals rfl

theorem atot10319 : totK PD2M8K2 D2M8K2.u10319 = [0, 0, 356035180752, 962239817024, 459248413819, 21796010231, 0, 0] := by
  rw [show D2M8K2.u10319 = KTree.node D2M8K2.t10324 (nat_lit 22586601) (nat_lit 1222665432) (nat_lit 0) D2M8K2.t10325 from rfl, totK_node, tot10324, tot10325]
  decide +kernel

theorem arows10320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10320 = true := by
  rw [show D2M8K2.u10320 = KTree.node D2M8K2.t10326 (nat_lit 22591977) (nat_lit 1890793090) (nat_lit 0) D2M8K2.t10327 from rfl, allE_node, rows10326, irow10320, rows10327]
  all_goals rfl

theorem atot10320 : totK PD2M8K2 D2M8K2.u10320 = [0, 0, 410014687115, 970425660402, 401624526529, 18572584944, 0, 0] := by
  rw [show D2M8K2.u10320 = KTree.node D2M8K2.t10326 (nat_lit 22591977) (nat_lit 1890793090) (nat_lit 0) D2M8K2.t10327 from rfl, totK_node, tot10326, tot10327]
  decide +kernel

theorem arows10323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10323 = true := by
  rw [show D2M8K2.u10323 = KTree.node D2M8K2.t10328 (nat_lit 22593491) (nat_lit 2779696588) (nat_lit 0) D2M8K2.t10329 from rfl, allE_node, rows10328, irow10323, rows10329]
  all_goals rfl

theorem atot10323 : totK PD2M8K2 D2M8K2.u10323 = [0, 0, 333770610371, 933573856234, 496139985624, 28666324267, 0, 0] := by
  rw [show D2M8K2.u10323 = KTree.node D2M8K2.t10328 (nat_lit 22593491) (nat_lit 2779696588) (nat_lit 0) D2M8K2.t10329 from rfl, totK_node, tot10328, tot10329]
  decide +kernel

theorem arows10324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10324 = true := by
  rw [show D2M8K2.u10324 = KTree.node D2M8K2.t10330 (nat_lit 22596506) (nat_lit 4225304539) (nat_lit 0) D2M8K2.t10331 from rfl, allE_node, rows10330, irow10324, rows10331]
  all_goals rfl

theorem atot10324 : totK PD2M8K2 D2M8K2.u10324 = [0, 0, 262159433119, 824670606737, 580705290599, 78365794853, 1095107716, 0] := by
  rw [show D2M8K2.u10324 = KTree.node D2M8K2.t10330 (nat_lit 22596506) (nat_lit 4225304539) (nat_lit 0) D2M8K2.t10331 from rfl, totK_node, tot10330, tot10331]
  decide +kernel

theorem arows10326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10326 = true := by
  rw [show D2M8K2.u10326 = KTree.node D2M8K2.t10332 (nat_lit 22602249) (nat_lit 1815697724) (nat_lit 0) D2M8K2.t10333 from rfl, allE_node, rows10332, irow10326, rows10333]
  all_goals rfl

theorem atot10326 : totK PD2M8K2 D2M8K2.u10326 = [0, 218074617895, 490703766819, 472299503052, 470051106262, 111341065102, 3882006667, 0] := by
  rw [show D2M8K2.u10326 = KTree.node D2M8K2.t10332 (nat_lit 22602249) (nat_lit 1815697724) (nat_lit 0) D2M8K2.t10333 from rfl, totK_node, tot10332, tot10333]
  decide +kernel

theorem arows10327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10327 = true := by
  rw [show D2M8K2.u10327 = KTree.node D2M8K2.t10334 (nat_lit 22603832) (nat_lit 2679048941) (nat_lit 0) D2M8K2.t10335 from rfl, allE_node, rows10334, irow10327, rows10335]
  all_goals rfl

theorem atot10327 : totK PD2M8K2 D2M8K2.u10327 = [0, 189578890932, 757576295511, 715605914310, 117589265327, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10327 = KTree.node D2M8K2.t10334 (nat_lit 22603832) (nat_lit 2679048941) (nat_lit 0) D2M8K2.t10335 from rfl, totK_node, tot10334, tot10335]
  decide +kernel

theorem arows10332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10332 = true := by
  rw [show D2M8K2.u10332 = KTree.node D2M8K2.t10336 (nat_lit 22606193) (nat_lit 1737104167) (nat_lit 0) D2M8K2.t10337 from rfl, allE_node, rows10336, irow10332, rows10337]
  all_goals rfl

theorem atot10332 : totK PD2M8K2 D2M8K2.u10332 = [0, 260041460560, 830312117101, 665437274557, 76436430549, 0, 0, 0] := by
  rw [show D2M8K2.u10332 = KTree.node D2M8K2.t10336 (nat_lit 22606193) (nat_lit 1737104167) (nat_lit 0) D2M8K2.t10337 from rfl, totK_node, tot10336, tot10337]
  decide +kernel

theorem arows10333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10333 = true := by
  rw [show D2M8K2.u10333 = KTree.node D2M8K2.t10338 (nat_lit 22607753) (nat_lit 1794605220) (nat_lit 0) D2M8K2.t10339 from rfl, allE_node, rows10338, irow10333, rows10339]
  all_goals rfl

theorem atot10333 : totK PD2M8K2 D2M8K2.u10333 = [0, 159080229232, 646334028862, 717715083226, 273312281911, 23787324087, 0, 0] := by
  rw [show D2M8K2.u10333 = KTree.node D2M8K2.t10338 (nat_lit 22607753) (nat_lit 1794605220) (nat_lit 0) D2M8K2.t10339 from rfl, totK_node, tot10338, tot10339]
  decide +kernel

theorem arows10335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10335 = true := by
  rw [show D2M8K2.u10335 = KTree.node D2M8K2.t10340 (nat_lit 22609001) (nat_lit 1606792162) (nat_lit 0) D2M8K2.t10341 from rfl, allE_node, rows10340, irow10335, rows10341]
  all_goals rfl

theorem atot10335 : totK PD2M8K2 D2M8K2.u10335 = [0, 164773433953, 592495097588, 747335197328, 298928573388, 12229515597, 0, 0] := by
  rw [show D2M8K2.u10335 = KTree.node D2M8K2.t10340 (nat_lit 22609001) (nat_lit 1606792162) (nat_lit 0) D2M8K2.t10341 from rfl, totK_node, tot10340, tot10341]
  decide +kernel

theorem arows10336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10336 = true := by
  rw [show D2M8K2.u10336 = KTree.node D2M8K2.t10342 (nat_lit 22610861) (nat_lit 2149376973) (nat_lit 0) D2M8K2.t10343 from rfl, allE_node, rows10342, irow10336, rows10343]
  all_goals rfl

theorem atot10336 : totK PD2M8K2 D2M8K2.u10336 = [0, 161825429135, 700266903033, 790232080875, 154737887191, 2309606161, 0, 0] := by
  rw [show D2M8K2.u10336 = KTree.node D2M8K2.t10342 (nat_lit 22610861) (nat_lit 2149376973) (nat_lit 0) D2M8K2.t10343 from rfl, totK_node, tot10342, tot10343]
  decide +kernel

theorem arows10339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10339 = true := by
  rw [show D2M8K2.u10339 = KTree.node D2M8K2.t10344 (nat_lit 22613022) (nat_lit 3902705292) (nat_lit 0) D2M8K2.t10345 from rfl, allE_node, rows10344, irow10339, rows10345]
  all_goals rfl

theorem atot10339 : totK PD2M8K2 D2M8K2.u10339 = [0, 333485645173, 864057479327, 549860868536, 84910092071, 3089224145, 0, 0] := by
  rw [show D2M8K2.u10339 = KTree.node D2M8K2.t10344 (nat_lit 22613022) (nat_lit 3902705292) (nat_lit 0) D2M8K2.t10345 from rfl, totK_node, tot10344, tot10345]
  decide +kernel

theorem arows10340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10340 = true := by
  rw [show D2M8K2.u10340 = KTree.node D2M8K2.t10346 (nat_lit 22614500) (nat_lit 2472952055) (nat_lit 0) D2M8K2.t10347 from rfl, allE_node, rows10346, irow10340, rows10347]
  all_goals rfl

theorem atot10340 : totK PD2M8K2 D2M8K2.u10340 = [0, 89753051296, 626476972428, 847241390425, 224534822856, 9664716404, 0, 0] := by
  rw [show D2M8K2.u10340 = KTree.node D2M8K2.t10346 (nat_lit 22614500) (nat_lit 2472952055) (nat_lit 0) D2M8K2.t10347 from rfl, totK_node, tot10346, tot10347]
  decide +kernel

theorem arows10342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10342 = true := by
  rw [show D2M8K2.u10342 = KTree.node D2M8K2.t10348 (nat_lit 22619850) (nat_lit 3863973587) (nat_lit 0) D2M8K2.t10349 from rfl, allE_node, rows10348, irow10342, rows10349]
  all_goals rfl

theorem atot10342 : totK PD2M8K2 D2M8K2.u10342 = [0, 276873712750, 802787079268, 615266550097, 118277249997, 3579068459, 0, 0] := by
  rw [show D2M8K2.u10342 = KTree.node D2M8K2.t10348 (nat_lit 22619850) (nat_lit 3863973587) (nat_lit 0) D2M8K2.t10349 from rfl, totK_node, tot10348, tot10349]
  decide +kernel

theorem arows10343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10343 = true := by
  rw [show D2M8K2.u10343 = KTree.node D2M8K2.t10350 (nat_lit 22621261) (nat_lit 1389971820) (nat_lit 0) D2M8K2.t10351 from rfl, allE_node, rows10350, irow10343, rows10351]
  all_goals rfl

theorem atot10343 : totK PD2M8K2 D2M8K2.u10343 = [0, 164986643072, 699749393627, 785702173561, 166782191832, 2304167554, 0, 0] := by
  rw [show D2M8K2.u10343 = KTree.node D2M8K2.t10350 (nat_lit 22621261) (nat_lit 1389971820) (nat_lit 0) D2M8K2.t10351 from rfl, totK_node, tot10350, tot10351]
  decide +kernel

theorem arows10347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10347 = true := by
  rw [show D2M8K2.u10347 = KTree.node D2M8K2.t10352 (nat_lit 22622923) (nat_lit 1498967415) (nat_lit 0) D2M8K2.t10353 from rfl, allE_node, rows10352, irow10347, rows10353]
  all_goals rfl

theorem atot10347 : totK PD2M8K2 D2M8K2.u10347 = [0, 0, 379807075937, 960600345441, 416406959417, 22265617646, 0, 0] := by
  rw [show D2M8K2.u10347 = KTree.node D2M8K2.t10352 (nat_lit 22622923) (nat_lit 1498967415) (nat_lit 0) D2M8K2.t10353 from rfl, totK_node, tot10352, tot10353]
  decide +kernel

theorem arows10348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10348 = true := by
  rw [show D2M8K2.u10348 = KTree.node D2M8K2.t10354 (nat_lit 22624567) (nat_lit 1861168518) (nat_lit 0) D2M8K2.t10355 from rfl, allE_node, rows10354, irow10348, rows10355]
  all_goals rfl

theorem atot10348 : totK PD2M8K2 D2M8K2.u10348 = [0, 0, 207670934380, 779152704243, 680700424540, 86267590779, 1310285577, 0] := by
  rw [show D2M8K2.u10348 = KTree.node D2M8K2.t10354 (nat_lit 22624567) (nat_lit 1861168518) (nat_lit 0) D2M8K2.t10355 from rfl, totK_node, tot10354, tot10355]
  decide +kernel

theorem arows10350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10350 = true := by
  rw [show D2M8K2.u10350 = KTree.node D2M8K2.t10356 (nat_lit 22626954) (nat_lit 3816600073) (nat_lit 0) D2M8K2.t10357 from rfl, allE_node, rows10356, irow10350, rows10357]
  all_goals rfl

theorem atot10350 : totK PD2M8K2 D2M8K2.u10350 = [0, 0, 259278204842, 836286926055, 658769812714, 59244814932, 0, 0] := by
  rw [show D2M8K2.u10350 = KTree.node D2M8K2.t10356 (nat_lit 22626954) (nat_lit 3816600073) (nat_lit 0) D2M8K2.t10357 from rfl, totK_node, tot10356, tot10357]
  decide +kernel

theorem arows10351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10351 = true := by
  rw [show D2M8K2.u10351 = KTree.node D2M8K2.t10358 (nat_lit 22629970) (nat_lit 3773431234) (nat_lit 0) D2M8K2.t10359 from rfl, allE_node, rows10358, irow10351, rows10359]
  all_goals rfl

theorem atot10351 : totK PD2M8K2 D2M8K2.u10351 = [0, 0, 395480305139, 946828457039, 458434218110, 33917501677, 0, 0] := by
  rw [show D2M8K2.u10351 = KTree.node D2M8K2.t10358 (nat_lit 22629970) (nat_lit 3773431234) (nat_lit 0) D2M8K2.t10359 from rfl, totK_node, tot10358, tot10359]
  decide +kernel

theorem arows10354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10354 = true := by
  rw [show D2M8K2.u10354 = KTree.node D2M8K2.t10360 (nat_lit 22631856) (nat_lit 3318676690) (nat_lit 0) D2M8K2.t10361 from rfl, allE_node, rows10360, irow10354, rows10361]
  all_goals rfl

theorem atot10354 : totK PD2M8K2 D2M8K2.u10354 = [0, 0, 173064775043, 805508754849, 729221981044, 81959488091, 1075657031, 0] := by
  rw [show D2M8K2.u10354 = KTree.node D2M8K2.t10360 (nat_lit 22631856) (nat_lit 3318676690) (nat_lit 0) D2M8K2.t10361 from rfl, totK_node, tot10360, tot10361]
  decide +kernel

theorem arows10355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10355 = true := by
  rw [show D2M8K2.u10355 = KTree.node D2M8K2.t10362 (nat_lit 22634446) (nat_lit 3029894573) (nat_lit 0) D2M8K2.t10363 from rfl, allE_node, rows10362, irow10355, rows10363]
  all_goals rfl

theorem atot10355 : totK PD2M8K2 D2M8K2.u10355 = [0, 0, 340773383225, 916167543405, 522971719020, 44650306665, 0, 0] := by
  rw [show D2M8K2.u10355 = KTree.node D2M8K2.t10362 (nat_lit 22634446) (nat_lit 3029894573) (nat_lit 0) D2M8K2.t10363 from rfl, totK_node, tot10362, tot10363]
  decide +kernel

theorem arows10357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10357 = true := by
  rw [show D2M8K2.u10357 = KTree.node D2M8K2.t10364 (nat_lit 22636185) (nat_lit 1626216548) (nat_lit 0) D2M8K2.t10365 from rfl, allE_node, rows10364, irow10357, rows10365]
  all_goals rfl

theorem atot10357 : totK PD2M8K2 D2M8K2.u10357 = [0, 0, 123863213820, 663869519998, 791256950578, 169304897981, 4931404646, 0] := by
  rw [show D2M8K2.u10357 = KTree.node D2M8K2.t10364 (nat_lit 22636185) (nat_lit 1626216548) (nat_lit 0) D2M8K2.t10365 from rfl, totK_node, tot10364, tot10365]
  decide +kernel

theorem arows10358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10358 = true := by
  rw [show D2M8K2.u10358 = KTree.node D2M8K2.t10366 (nat_lit 22641199) (nat_lit 2447780778) (nat_lit 0) D2M8K2.t10367 from rfl, allE_node, rows10366, irow10358, rows10367]
  all_goals rfl

theorem atot10358 : totK PD2M8K2 D2M8K2.u10358 = [0, 0, 316428611838, 898283168086, 567798264625, 46139499479, 0, 0] := by
  rw [show D2M8K2.u10358 = KTree.node D2M8K2.t10366 (nat_lit 22641199) (nat_lit 2447780778) (nat_lit 0) D2M8K2.t10367 from rfl, totK_node, tot10366, tot10367]
  decide +kernel

theorem arows10365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10365 = true := by
  rw [show D2M8K2.u10365 = KTree.node D2M8K2.t10368 (nat_lit 22642892) (nat_lit 2167070296) (nat_lit 0) D2M8K2.t10369 from rfl, allE_node, rows10368, irow10365, rows10369]
  all_goals rfl

theorem atot10365 : totK PD2M8K2 D2M8K2.u10365 = [0, 0, 55388964612, 452120467563, 888562318350, 329221858392, 17369593618, 0] := by
  rw [show D2M8K2.u10365 = KTree.node D2M8K2.t10368 (nat_lit 22642892) (nat_lit 2167070296) (nat_lit 0) D2M8K2.t10369 from rfl, totK_node, tot10368, tot10369]
  decide +kernel

theorem arows10366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10366 = true := by
  rw [show D2M8K2.u10366 = KTree.node D2M8K2.t10370 (nat_lit 22644707) (nat_lit 2952672172) (nat_lit 0) D2M8K2.t10371 from rfl, allE_node, rows10370, irow10366, rows10371]
  all_goals rfl

theorem atot10366 : totK PD2M8K2 D2M8K2.u10366 = [0, 0, 379463992477, 962955354390, 423399435150, 18676781250, 0, 0] := by
  rw [show D2M8K2.u10366 = KTree.node D2M8K2.t10370 (nat_lit 22644707) (nat_lit 2952672172) (nat_lit 0) D2M8K2.t10371 from rfl, totK_node, tot10370, tot10371]
  decide +kernel

theorem arows10368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10368 = true := by
  rw [show D2M8K2.u10368 = KTree.node D2M8K2.t10372 (nat_lit 22646388) (nat_lit 3244651262) (nat_lit 0) D2M8K2.t10373 from rfl, allE_node, rows10372, irow10368, rows10373]
  all_goals rfl

theorem atot10368 : totK PD2M8K2 D2M8K2.u10368 = [0, 0, 86643100371, 673020021566, 893929100897, 138679209925, 1369150432, 0] := by
  rw [show D2M8K2.u10368 = KTree.node D2M8K2.t10372 (nat_lit 22646388) (nat_lit 3244651262) (nat_lit 0) D2M8K2.t10373 from rfl, totK_node, tot10372, tot10373]
  decide +kernel

theorem arows10369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10369 = true := by
  rw [show D2M8K2.u10369 = KTree.node D2M8K2.t10374 (nat_lit 22652128) (nat_lit 3756584681) (nat_lit 0) D2M8K2.t10375 from rfl, allE_node, rows10374, irow10369, rows10375]
  all_goals rfl

theorem atot10369 : totK PD2M8K2 D2M8K2.u10369 = [0, 0, 233640203949, 826598532086, 616112610527, 61059637619, 1164319620, 0] := by
  rw [show D2M8K2.u10369 = KTree.node D2M8K2.t10374 (nat_lit 22652128) (nat_lit 3756584681) (nat_lit 0) D2M8K2.t10375 from rfl, totK_node, tot10374, tot10375]
  decide +kernel

theorem arows10372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10372 = true := by
  rw [show D2M8K2.u10372 = KTree.node D2M8K2.t10376 (nat_lit 22654558) (nat_lit 3723000701) (nat_lit 0) D2M8K2.t10377 from rfl, allE_node, rows10376, irow10372, rows10377]
  all_goals rfl

theorem atot10372 : totK PD2M8K2 D2M8K2.u10372 = [0, 0, 337295246807, 914161754471, 525605369519, 41380977627, 0, 0] := by
  rw [show D2M8K2.u10372 = KTree.node D2M8K2.t10376 (nat_lit 22654558) (nat_lit 3723000701) (nat_lit 0) D2M8K2.t10377 from rfl, totK_node, tot10376, tot10377]
  decide +kernel

theorem arows10373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10373 = true := by
  rw [show D2M8K2.u10373 = KTree.node D2M8K2.t10378 (nat_lit 22656053) (nat_lit 1083866740) (nat_lit 0) D2M8K2.t10379 from rfl, allE_node, rows10378, irow10373, rows10379]
  all_goals rfl

theorem atot10373 : totK PD2M8K2 D2M8K2.u10373 = [0, 0, 86588537956, 609068571034, 847476809838, 223860998181, 9668735432, 0] := by
  rw [show D2M8K2.u10373 = KTree.node D2M8K2.t10378 (nat_lit 22656053) (nat_lit 1083866740) (nat_lit 0) D2M8K2.t10379 from rfl, totK_node, tot10378, tot10379]
  decide +kernel

theorem arows10375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10375 = true := by
  rw [show D2M8K2.u10375 = KTree.node D2M8K2.t10380 (nat_lit 22657902) (nat_lit 3983372916) (nat_lit 0) D2M8K2.t10381 from rfl, allE_node, rows10380, irow10375, rows10381]
  all_goals rfl

theorem atot10375 : totK PD2M8K2 D2M8K2.u10375 = [0, 0, 316805839034, 810784712700, 525224573432, 97059692601, 3521263076, 0] := by
  rw [show D2M8K2.u10375 = KTree.node D2M8K2.t10380 (nat_lit 22657902) (nat_lit 3983372916) (nat_lit 0) D2M8K2.t10381 from rfl, totK_node, tot10380, tot10381]
  decide +kernel

theorem arows10376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10376 = true := by
  rw [show D2M8K2.u10376 = KTree.node D2M8K2.t10382 (nat_lit 22659480) (nat_lit 3462157730) (nat_lit 0) D2M8K2.t10383 from rfl, allE_node, rows10382, irow10376, rows10383]
  all_goals rfl

theorem atot10376 : totK PD2M8K2 D2M8K2.u10376 = [0, 0, 90564426449, 705749500905, 854375346268, 116562912068, 1096505104, 0] := by
  rw [show D2M8K2.u10376 = KTree.node D2M8K2.t10382 (nat_lit 22659480) (nat_lit 3462157730) (nat_lit 0) D2M8K2.t10383 from rfl, totK_node, tot10382, tot10383]
  decide +kernel

theorem arows10380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10380 = true := by
  rw [show D2M8K2.u10380 = KTree.node D2M8K2.t10384 (nat_lit 22661572) (nat_lit 3847744678) (nat_lit 0) D2M8K2.t10385 from rfl, allE_node, rows10384, irow10380, rows10385]
  all_goals rfl

theorem atot10380 : totK PD2M8K2 D2M8K2.u10380 = [0, 0, 374157906229, 870593515951, 478716339145, 83353603775, 3821179711, 0] := by
  rw [show D2M8K2.u10380 = KTree.node D2M8K2.t10384 (nat_lit 22661572) (nat_lit 3847744678) (nat_lit 0) D2M8K2.t10385 from rfl, totK_node, tot10384, tot10385]
  decide +kernel

theorem arows10381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10381 = true := by
  rw [show D2M8K2.u10381 = KTree.node D2M8K2.t10386 (nat_lit 22663307) (nat_lit 2887599041) (nat_lit 0) D2M8K2.t10387 from rfl, allE_node, rows10386, irow10381, rows10387]
  all_goals rfl

theorem atot10381 : totK PD2M8K2 D2M8K2.u10381 = [0, 0, 38115386132, 567740057185, 931718974548, 239245330490, 6186994463, 0] := by
  rw [show D2M8K2.u10381 = KTree.node D2M8K2.t10386 (nat_lit 22663307) (nat_lit 2887599041) (nat_lit 0) D2M8K2.t10387 from rfl, totK_node, tot10386, tot10387]
  decide +kernel

theorem arows10383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10383 = true := by
  rw [show D2M8K2.u10383 = KTree.node D2M8K2.t10388 (nat_lit 22665356) (nat_lit 3502065492) (nat_lit 0) D2M8K2.t10389 from rfl, allE_node, rows10388, irow10383, rows10389]
  all_goals rfl

theorem atot10383 : totK PD2M8K2 D2M8K2.u10383 = [0, 0, 0, 398491647426, 948956446202, 369646347701, 22196159091, 0] := by
  rw [show D2M8K2.u10383 = KTree.node D2M8K2.t10388 (nat_lit 22665356) (nat_lit 3502065492) (nat_lit 0) D2M8K2.t10389 from rfl, totK_node, tot10388, tot10389]
  decide +kernel

theorem arows10384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10384 = true := by
  rw [show D2M8K2.u10384 = KTree.node D2M8K2.t10390 (nat_lit 22667123) (nat_lit 2724120209) (nat_lit 0) D2M8K2.t10391 from rfl, allE_node, rows10390, irow10384, rows10391]
  all_goals rfl

theorem atot10384 : totK PD2M8K2 D2M8K2.u10384 = [0, 0, 0, 115270960353, 762171037395, 709610671410, 103420085930, 1310517177] := by
  rw [show D2M8K2.u10384 = KTree.node D2M8K2.t10390 (nat_lit 22667123) (nat_lit 2724120209) (nat_lit 0) D2M8K2.t10391 from rfl, totK_node, tot10390, tot10391]
  decide +kernel

theorem arows10387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10387 = true := by
  rw [show D2M8K2.u10387 = KTree.node D2M8K2.t10392 (nat_lit 22674925) (nat_lit 1132023364) (nat_lit 0) D2M8K2.t10393 from rfl, allE_node, rows10392, irow10387, rows10393]
  all_goals rfl

theorem atot10387 : totK PD2M8K2 D2M8K2.u10387 = [0, 0, 0, 478637522848, 994048072305, 295692945090, 7727078391, 0] := by
  rw [show D2M8K2.u10387 = KTree.node D2M8K2.t10392 (nat_lit 22674925) (nat_lit 1132023364) (nat_lit 0) D2M8K2.t10393 from rfl, totK_node, tot10392, tot10393]
  decide +kernel

theorem arows10388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10388 = true := by
  rw [show D2M8K2.u10388 = KTree.node D2M8K2.t10394 (nat_lit 22676520) (nat_lit 3424999657) (nat_lit 0) D2M8K2.t10395 from rfl, allE_node, rows10394, irow10388, rows10395]
  all_goals rfl

theorem atot10388 : totK PD2M8K2 D2M8K2.u10388 = [0, 0, 0, 388669485048, 934208126022, 389039868042, 22521289395, 0] := by
  rw [show D2M8K2.u10388 = KTree.node D2M8K2.t10394 (nat_lit 22676520) (nat_lit 3424999657) (nat_lit 0) D2M8K2.t10395 from rfl, totK_node, tot10394, tot10395]
  decide +kernel

theorem arows10390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10390 = true := by
  rw [show D2M8K2.u10390 = KTree.node D2M8K2.t10396 (nat_lit 22679596) (nat_lit 3542420630) (nat_lit 0) D2M8K2.t10397 from rfl, allE_node, rows10396, irow10390, rows10397]
  all_goals rfl

theorem atot10390 : totK PD2M8K2 D2M8K2.u10390 = [0, 0, 0, 435366517765, 976660155867, 335362693118, 14725817229, 0] := by
  rw [show D2M8K2.u10390 = KTree.node D2M8K2.t10396 (nat_lit 22679596) (nat_lit 3542420630) (nat_lit 0) D2M8K2.t10397 from rfl, totK_node, tot10396, tot10397]
  decide +kernel

theorem arows10391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10391 = true := by
  rw [show D2M8K2.u10391 = KTree.node D2M8K2.t10398 (nat_lit 22688992) (nat_lit 3751831776) (nat_lit 0) D2M8K2.t10399 from rfl, allE_node, rows10398, irow10391, rows10399]
  all_goals rfl

theorem atot10391 : totK PD2M8K2 D2M8K2.u10391 = [0, 0, 211587284169, 668735060494, 711774856325, 226994434191, 12810146349, 0] := by
  rw [show D2M8K2.u10391 = KTree.node D2M8K2.t10398 (nat_lit 22688992) (nat_lit 3751831776) (nat_lit 0) D2M8K2.t10399 from rfl, totK_node, tot10398, tot10399]
  decide +kernel

theorem arows10396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10396 = true := by
  rw [show D2M8K2.u10396 = KTree.node D2M8K2.t10400 (nat_lit 22690158) (nat_lit 4025775211) (nat_lit 0) D2M8K2.t10401 from rfl, allE_node, rows10400, irow10396, rows10401]
  all_goals rfl

theorem atot10396 : totK PD2M8K2 D2M8K2.u10396 = [0, 0, 231717615600, 784221470942, 633815348959, 173999184956, 15073499398, 0] := by
  rw [show D2M8K2.u10396 = KTree.node D2M8K2.t10400 (nat_lit 22690158) (nat_lit 4025775211) (nat_lit 0) D2M8K2.t10401 from rfl, totK_node, tot10400, tot10401]
  decide +kernel

theorem arows10397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10397 = true := by
  rw [show D2M8K2.u10397 = KTree.node D2M8K2.t10402 (nat_lit 22691840) (nat_lit 3241997085) (nat_lit 0) D2M8K2.t10403 from rfl, allE_node, rows10402, irow10397, rows10403]
  all_goals rfl

theorem atot10397 : totK PD2M8K2 D2M8K2.u10397 = [0, 0, 127922347197, 553877822555, 860807371195, 286315891354, 9669829517, 0] := by
  rw [show D2M8K2.u10397 = KTree.node D2M8K2.t10402 (nat_lit 22691840) (nat_lit 3241997085) (nat_lit 0) D2M8K2.t10403 from rfl, totK_node, tot10402, tot10403]
  decide +kernel

theorem arows10399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10399 = true := by
  rw [show D2M8K2.u10399 = KTree.node D2M8K2.t10404 (nat_lit 22695630) (nat_lit 4020059809) (nat_lit 0) D2M8K2.t10405 from rfl, allE_node, rows10404, irow10399, rows10405]
  all_goals rfl

theorem atot10399 : totK PD2M8K2 D2M8K2.u10399 = [0, 0, 415865984724, 983899894352, 424984808537, 30345906968, 0, 0] := by
  rw [show D2M8K2.u10399 = KTree.node D2M8K2.t10404 (nat_lit 22695630) (nat_lit 4020059809) (nat_lit 0) D2M8K2.t10405 from rfl, totK_node, tot10404, tot10405]
  decide +kernel

theorem arows10400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10400 = true := by
  rw [show D2M8K2.u10400 = KTree.node D2M8K2.t10406 (nat_lit 22697085) (nat_lit 1400863465) (nat_lit 0) D2M8K2.t10407 from rfl, allE_node, rows10406, irow10400, rows10407]
  all_goals rfl

theorem atot10400 : totK PD2M8K2 D2M8K2.u10400 = [0, 0, 209162817664, 822793088765, 698842553576, 80768858452, 0, 0] := by
  rw [show D2M8K2.u10400 = KTree.node D2M8K2.t10406 (nat_lit 22697085) (nat_lit 1400863465) (nat_lit 0) D2M8K2.t10407 from rfl, totK_node, tot10406, tot10407]
  decide +kernel

theorem arows10403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10403 = true := by
  rw [show D2M8K2.u10403 = KTree.node D2M8K2.t10408 (nat_lit 22699060) (nat_lit 3086661038) (nat_lit 0) D2M8K2.t10409 from rfl, allE_node, rows10408, irow10403, rows10409]
  all_goals rfl

theorem atot10403 : totK PD2M8K2 D2M8K2.u10403 = [0, 0, 222024027054, 671620662420, 695943741520, 194187131146, 11012983587, 0] := by
  rw [show D2M8K2.u10403 = KTree.node D2M8K2.t10408 (nat_lit 22699060) (nat_lit 3086661038) (nat_lit 0) D2M8K2.t10409 from rfl, totK_node, tot10408, tot10409]
  decide +kernel

theorem arows10404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10404 = true := by
  rw [show D2M8K2.u10404 = KTree.node D2M8K2.t10410 (nat_lit 22700330) (nat_lit 4182302026) (nat_lit 0) D2M8K2.t10411 from rfl, allE_node, rows10410, irow10404, rows10411]
  all_goals rfl

theorem atot10404 : totK PD2M8K2 D2M8K2.u10404 = [0, 0, 188758057182, 854106043725, 698749251573, 67027553262, 0, 0] := by
  rw [show D2M8K2.u10404 = KTree.node D2M8K2.t10410 (nat_lit 22700330) (nat_lit 4182302026) (nat_lit 0) D2M8K2.t10411 from rfl, totK_node, tot10410, tot10411]
  decide +kernel

theorem arows10406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10406 = true := by
  rw [show D2M8K2.u10406 = KTree.node D2M8K2.t10412 (nat_lit 22702872) (nat_lit 3009515013) (nat_lit 0) D2M8K2.t10413 from rfl, allE_node, rows10412, irow10406, rows10413]
  all_goals rfl

theorem atot10406 : totK PD2M8K2 D2M8K2.u10406 = [0, 0, 323566031651, 842265089609, 570908219293, 96191498650, 2813333534, 0] := by
  rw [show D2M8K2.u10406 = KTree.node D2M8K2.t10412 (nat_lit 22702872) (nat_lit 3009515013) (nat_lit 0) D2M8K2.t10413 from rfl, totK_node, tot10412, tot10413]
  decide +kernel

theorem arows10407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10407 = true := by
  rw [show D2M8K2.u10407 = KTree.node D2M8K2.t10414 (nat_lit 22704555) (nat_lit 3690903724) (nat_lit 0) D2M8K2.t10415 from rfl, allE_node, rows10414, irow10407, rows10415]
  all_goals rfl

theorem atot10407 : totK PD2M8K2 D2M8K2.u10407 = [0, 0, 91991626324, 715940524204, 852671706156, 159131312995, 3718846349, 0] := by
  rw [show D2M8K2.u10407 = KTree.node D2M8K2.t10414 (nat_lit 22704555) (nat_lit 3690903724) (nat_lit 0) D2M8K2.t10415 from rfl, totK_node, tot10414, tot10415]
  decide +kernel

theorem arows10411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10411 = true := by
  rw [show D2M8K2.u10411 = KTree.node D2M8K2.t10416 (nat_lit 22768964) (nat_lit 3194752778) (nat_lit 0) D2M8K2.t10417 from rfl, allE_node, rows10416, irow10411, rows10417]
  all_goals rfl

theorem atot10411 : totK PD2M8K2 D2M8K2.u10411 = [0, 0, 342470890994, 835819117386, 464166261111, 108487667018, 8913356732, 0] := by
  rw [show D2M8K2.u10411 = KTree.node D2M8K2.t10416 (nat_lit 22768964) (nat_lit 3194752778) (nat_lit 0) D2M8K2.t10417 from rfl, totK_node, tot10416, tot10417]
  decide +kernel

theorem arows10412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10412 = true := by
  rw [show D2M8K2.u10412 = KTree.node D2M8K2.t10418 (nat_lit 22770500) (nat_lit 3003686569) (nat_lit 0) D2M8K2.t10419 from rfl, allE_node, rows10418, irow10412, rows10419]
  all_goals rfl

theorem atot10412 : totK PD2M8K2 D2M8K2.u10412 = [0, 0, 107734653192, 681481476159, 854424740835, 133655536579, 1369150432, 0] := by
  rw [show D2M8K2.u10412 = KTree.node D2M8K2.t10418 (nat_lit 22770500) (nat_lit 3003686569) (nat_lit 0) D2M8K2.t10419 from rfl, totK_node, tot10418, tot10419]
  decide +kernel

theorem arows10414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10414 = true := by
  rw [show D2M8K2.u10414 = KTree.node D2M8K2.t10420 (nat_lit 22772581) (nat_lit 1275912670) (nat_lit 0) D2M8K2.t10421 from rfl, allE_node, rows10420, irow10414, rows10421]
  all_goals rfl

theorem atot10414 : totK PD2M8K2 D2M8K2.u10414 = [0, 0, 383505378551, 936557539646, 473350970666, 36489984964, 0, 0] := by
  rw [show D2M8K2.u10414 = KTree.node D2M8K2.t10420 (nat_lit 22772581) (nat_lit 1275912670) (nat_lit 0) D2M8K2.t10421 from rfl, totK_node, tot10420, tot10421]
  decide +kernel

theorem arows10415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10415 = true := by
  rw [show D2M8K2.u10415 = KTree.node D2M8K2.t10422 (nat_lit 22774223) (nat_lit 2122592225) (nat_lit 0) D2M8K2.t10423 from rfl, allE_node, rows10422, irow10415, rows10423]
  all_goals rfl

theorem atot10415 : totK PD2M8K2 D2M8K2.u10415 = [0, 0, 0, 481802445165, 956450763190, 348431998070, 20504164489, 0] := by
  rw [show D2M8K2.u10415 = KTree.node D2M8K2.t10422 (nat_lit 22774223) (nat_lit 2122592225) (nat_lit 0) D2M8K2.t10423 from rfl, totK_node, tot10422, tot10423]
  decide +kernel

theorem arows10418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10418 = true := by
  rw [show D2M8K2.u10418 = KTree.node D2M8K2.t10424 (nat_lit 22778981) (nat_lit 1311899060) (nat_lit 32) D2M8K2.t10425 from rfl, allE_node, rows10424, irow10418, rows10425]
  all_goals rfl

theorem atot10418 : totK PD2M8K2 D2M8K2.u10418 = [0, 0, 356780791970, 854905704470, 512069442957, 106938627700, 4239164426, 0] := by
  rw [show D2M8K2.u10418 = KTree.node D2M8K2.t10424 (nat_lit 22778981) (nat_lit 1311899060) (nat_lit 32) D2M8K2.t10425 from rfl, totK_node, tot10424, tot10425]
  decide +kernel

theorem arows10419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10419 = true := by
  rw [show D2M8K2.u10419 = KTree.node D2M8K2.t10426 (nat_lit 22780446) (nat_lit 3971648693) (nat_lit 0) D2M8K2.t10427 from rfl, allE_node, rows10426, irow10419, rows10427]
  all_goals rfl

theorem atot10419 : totK PD2M8K2 D2M8K2.u10419 = [0, 0, 88554027754, 620811504934, 859266254382, 224220599760, 9668735432, 0] := by
  rw [show D2M8K2.u10419 = KTree.node D2M8K2.t10426 (nat_lit 22780446) (nat_lit 3971648693) (nat_lit 0) D2M8K2.t10427 from rfl, totK_node, tot10426, tot10427]
  decide +kernel

theorem arows10421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10421 = true := by
  rw [show D2M8K2.u10421 = KTree.node D2M8K2.t10428 (nat_lit 22782274) (nat_lit 3843205375) (nat_lit 0) D2M8K2.t10429 from rfl, allE_node, rows10428, irow10421, rows10429]
  all_goals rfl

theorem atot10421 : totK PD2M8K2 D2M8K2.u10421 = [0, 0, 288257570434, 776936478792, 590403809332, 115194532372, 3581949829, 0] := by
  rw [show D2M8K2.u10421 = KTree.node D2M8K2.t10428 (nat_lit 22782274) (nat_lit 3843205375) (nat_lit 0) D2M8K2.t10429 from rfl, totK_node, tot10428, tot10429]
  decide +kernel

theorem arows10422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10422 = true := by
  rw [show D2M8K2.u10422 = KTree.node D2M8K2.t10430 (nat_lit 22783782) (nat_lit 3710900557) (nat_lit 0) D2M8K2.t10431 from rfl, allE_node, rows10430, irow10422, rows10431]
  all_goals rfl

theorem atot10422 : totK PD2M8K2 D2M8K2.u10422 = [0, 0, 128510068681, 739548209745, 808677949472, 112378300499, 1096505104, 0] := by
  rw [show D2M8K2.u10422 = KTree.node D2M8K2.t10430 (nat_lit 22783782) (nat_lit 3710900557) (nat_lit 0) D2M8K2.t10431 from rfl, totK_node, tot10430, tot10431]
  decide +kernel

theorem arows10428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10428 = true := by
  rw [show D2M8K2.u10428 = KTree.node D2M8K2.t10432 (nat_lit 22785794) (nat_lit 4084670007) (nat_lit 0) D2M8K2.t10433 from rfl, allE_node, rows10432, irow10428, rows10433]
  all_goals rfl

theorem atot10428 : totK PD2M8K2 D2M8K2.u10428 = [0, 0, 328448595242, 813733573411, 536809819596, 107556447525, 3884009855, 0] := by
  rw [show D2M8K2.u10428 = KTree.node D2M8K2.t10432 (nat_lit 22785794) (nat_lit 4084670007) (nat_lit 0) D2M8K2.t10433 from rfl, totK_node, tot10432, tot10433]
  decide +kernel

theorem arows10429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10429 = true := by
  rw [show D2M8K2.u10429 = KTree.node D2M8K2.t10434 (nat_lit 22787329) (nat_lit 1450128109) (nat_lit 0) D2M8K2.t10435 from rfl, allE_node, rows10434, irow10429, rows10435]
  all_goals rfl

theorem atot10429 : totK PD2M8K2 D2M8K2.u10429 = [0, 0, 92242864877, 634629931417, 860296794626, 200416602077, 5011483316, 0] := by
  rw [show D2M8K2.u10429 = KTree.node D2M8K2.t10434 (nat_lit 22787329) (nat_lit 1450128109) (nat_lit 0) D2M8K2.t10435 from rfl, totK_node, tot10434, tot10435]
  decide +kernel

theorem arows10431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10431 = true := by
  rw [show D2M8K2.u10431 = KTree.node D2M8K2.t10436 (nat_lit 22789489) (nat_lit 1507317077) (nat_lit 0) D2M8K2.t10437 from rfl, allE_node, rows10436, irow10431, rows10437]
  all_goals rfl

theorem atot10431 : totK PD2M8K2 D2M8K2.u10431 = [0, 0, 0, 416754608707, 952708738720, 365620543269, 20030192138, 0] := by
  rw [show D2M8K2.u10431 = KTree.node D2M8K2.t10436 (nat_lit 22789489) (nat_lit 1507317077) (nat_lit 0) D2M8K2.t10437 from rfl, totK_node, tot10436, tot10437]
  decide +kernel

theorem arows10432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10432 = true := by
  rw [show D2M8K2.u10432 = KTree.node D2M8K2.t10438 (nat_lit 22790794) (nat_lit 2552838554) (nat_lit 0) D2M8K2.t10439 from rfl, allE_node, rows10438, irow10432, rows10439]
  all_goals rfl

theorem atot10432 : totK PD2M8K2 D2M8K2.u10432 = [0, 0, 0, 104893635585, 723361356121, 765904420640, 109086847504, 1217496766] := by
  rw [show D2M8K2.u10432 = KTree.node D2M8K2.t10438 (nat_lit 22790794) (nat_lit 2552838554) (nat_lit 0) D2M8K2.t10439 from rfl, totK_node, tot10438, tot10439]
  decide +kernel

theorem arows10435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10435 = true := by
  rw [show D2M8K2.u10435 = KTree.node D2M8K2.t10440 (nat_lit 22793411) (nat_lit 2681780685) (nat_lit 0) D2M8K2.t10441 from rfl, allE_node, rows10440, irow10435, rows10441]
  all_goals rfl

theorem atot10435 : totK PD2M8K2 D2M8K2.u10435 = [0, 0, 0, 418568668913, 953739862937, 415052310423, 26596987813, 0] := by
  rw [show D2M8K2.u10435 = KTree.node D2M8K2.t10440 (nat_lit 22793411) (nat_lit 2681780685) (nat_lit 0) D2M8K2.t10441 from rfl, totK_node, tot10440, tot10441]
  decide +kernel

theorem arows10436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10436 = true := by
  rw [show D2M8K2.u10436 = KTree.node D2M8K2.t10442 (nat_lit 22800139) (nat_lit 1817206615) (nat_lit 0) D2M8K2.t10443 from rfl, allE_node, rows10442, irow10436, rows10443]
  all_goals rfl

theorem atot10436 : totK PD2M8K2 D2M8K2.u10436 = [0, 0, 0, 383289364259, 944978758418, 441631027473, 28716867054, 0] := by
  rw [show D2M8K2.u10436 = KTree.node D2M8K2.t10442 (nat_lit 22800139) (nat_lit 1817206615) (nat_lit 0) D2M8K2.t10443 from rfl, totK_node, tot10442, tot10443]
  decide +kernel

theorem arows10438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10438 = true := by
  rw [show D2M8K2.u10438 = KTree.node D2M8K2.t10444 (nat_lit 22801832) (nat_lit 3525495979) (nat_lit 0) D2M8K2.t10445 from rfl, allE_node, rows10444, irow10438, rows10445]
  all_goals rfl

theorem atot10438 : totK PD2M8K2 D2M8K2.u10438 = [0, 0, 0, 38122496643, 531290199249, 880454388972, 269680860474, 13105450397] := by
  rw [show D2M8K2.u10438 = KTree.node D2M8K2.t10444 (nat_lit 22801832) (nat_lit 3525495979) (nat_lit 0) D2M8K2.t10445 from rfl, totK_node, tot10444, tot10445]
  decide +kernel

theorem arows10439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10439 = true := by
  rw [show D2M8K2.u10439 = KTree.node D2M8K2.t10446 (nat_lit 22803230) (nat_lit 3551031102) (nat_lit 0) D2M8K2.t10447 from rfl, allE_node, rows10446, irow10439, rows10447]
  all_goals rfl

theorem atot10439 : totK PD2M8K2 D2M8K2.u10439 = [0, 0, 0, 372664689995, 913630829699, 434419074869, 32846886500, 0] := by
  rw [show D2M8K2.u10439 = KTree.node D2M8K2.t10446 (nat_lit 22803230) (nat_lit 3551031102) (nat_lit 0) D2M8K2.t10447 from rfl, totK_node, tot10446, tot10447]
  decide +kernel

theorem arows10443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10443 = true := by
  rw [show D2M8K2.u10443 = KTree.node D2M8K2.t10448 (nat_lit 22805026) (nat_lit 1938888866) (nat_lit 0) D2M8K2.t10449 from rfl, allE_node, rows10448, irow10443, rows10449]
  all_goals rfl

theorem atot10443 : totK PD2M8K2 D2M8K2.u10443 = [0, 0, 0, 119077466248, 653863633076, 738001124641, 151968773352, 4630915822] := by
  rw [show D2M8K2.u10443 = KTree.node D2M8K2.t10448 (nat_lit 22805026) (nat_lit 1938888866) (nat_lit 0) D2M8K2.t10449 from rfl, totK_node, tot10448, tot10449]
  decide +kernel

theorem arows10444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10444 = true := by
  rw [show D2M8K2.u10444 = KTree.node D2M8K2.t10450 (nat_lit 22807100) (nat_lit 3273071383) (nat_lit 0) D2M8K2.t10451 from rfl, allE_node, rows10450, irow10444, rows10451]
  all_goals rfl

theorem atot10444 : totK PD2M8K2 D2M8K2.u10444 = [0, 0, 72675911180, 441669053372, 873117413010, 401046031945, 24997195247, 0] := by
  rw [show D2M8K2.u10444 = KTree.node D2M8K2.t10450 (nat_lit 22807100) (nat_lit 3273071383) (nat_lit 0) D2M8K2.t10451 from rfl, totK_node, tot10450, tot10451]
  decide +kernel

theorem arows10446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10446 = true := by
  rw [show D2M8K2.u10446 = KTree.node D2M8K2.t10452 (nat_lit 22810680) (nat_lit 3428286285) (nat_lit 0) D2M8K2.t10453 from rfl, allE_node, rows10452, irow10446, rows10453]
  all_goals rfl

theorem atot10446 : totK PD2M8K2 D2M8K2.u10446 = [0, 0, 332405823575, 925246973225, 464996352181, 26491509441, 0, 0] := by
  rw [show D2M8K2.u10446 = KTree.node D2M8K2.t10452 (nat_lit 22810680) (nat_lit 3428286285) (nat_lit 0) D2M8K2.t10453 from rfl, totK_node, tot10452, tot10453]
  decide +kernel

theorem arows10447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10447 = true := by
  rw [show D2M8K2.u10447 = KTree.node D2M8K2.t10454 (nat_lit 22812537) (nat_lit 1855267513) (nat_lit 0) D2M8K2.t10455 from rfl, allE_node, rows10454, irow10447, rows10455]
  all_goals rfl

theorem atot10447 : totK PD2M8K2 D2M8K2.u10447 = [0, 0, 128013096128, 674362462241, 855409466430, 130709746101, 1310517177, 0] := by
  rw [show D2M8K2.u10447 = KTree.node D2M8K2.t10454 (nat_lit 22812537) (nat_lit 1855267513) (nat_lit 0) D2M8K2.t10455 from rfl, totK_node, tot10454, tot10455]
  decide +kernel

theorem arows10450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10450 = true := by
  rw [show D2M8K2.u10450 = KTree.node D2M8K2.t10456 (nat_lit 22814317) (nat_lit 1108564402) (nat_lit 0) D2M8K2.t10457 from rfl, allE_node, rows10456, irow10450, rows10457]
  all_goals rfl

theorem atot10450 : totK PD2M8K2 D2M8K2.u10450 = [0, 0, 283997553388, 848800714047, 568128620129, 123821050383, 8332571741, 0] := by
  rw [show D2M8K2.u10450 = KTree.node D2M8K2.t10456 (nat_lit 22814317) (nat_lit 1108564402) (nat_lit 0) D2M8K2.t10457 from rfl, totK_node, tot10456, tot10457]
  decide +kernel

theorem arows10451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10451 = true := by
  rw [show D2M8K2.u10451 = KTree.node D2M8K2.t10458 (nat_lit 22816152) (nat_lit 3046154136) (nat_lit 0) D2M8K2.t10459 from rfl, allE_node, rows10458, irow10451, rows10459]
  all_goals rfl

theorem atot10451 : totK PD2M8K2 D2M8K2.u10451 = [0, 0, 162798423720, 683553179803, 754980940673, 202996026374, 5411637735, 0] := by
  rw [show D2M8K2.u10451 = KTree.node D2M8K2.t10458 (nat_lit 22816152) (nat_lit 3046154136) (nat_lit 0) D2M8K2.t10459 from rfl, totK_node, tot10458, tot10459]
  decide +kernel

theorem arows10453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10453 = true := by
  rw [show D2M8K2.u10453 = KTree.node D2M8K2.t10460 (nat_lit 22818296) (nat_lit 3644536236) (nat_lit 0) D2M8K2.t10461 from rfl, allE_node, rows10460, irow10453, rows10461]
  all_goals rfl

theorem atot10453 : totK PD2M8K2 D2M8K2.u10453 = [0, 0, 159301758742, 763157606637, 732636415947, 99234691587, 2051644177, 0] := by
  rw [show D2M8K2.u10453 = KTree.node D2M8K2.t10460 (nat_lit 22818296) (nat_lit 3644536236) (nat_lit 0) D2M8K2.t10461 from rfl, totK_node, tot10460, tot10461]
  decide +kernel

theorem arows10454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10454 = true := by
  rw [show D2M8K2.u10454 = KTree.node D2M8K2.t10462 (nat_lit 22820512) (nat_lit 3118554472) (nat_lit 0) D2M8K2.t10463 from rfl, allE_node, rows10462, irow10454, rows10463]
  all_goals rfl

theorem atot10454 : totK PD2M8K2 D2M8K2.u10454 = [0, 0, 352671514424, 900628338860, 490618156159, 57269946941, 2481160468, 0] := by
  rw [show D2M8K2.u10454 = KTree.node D2M8K2.t10462 (nat_lit 22820512) (nat_lit 3118554472) (nat_lit 0) D2M8K2.t10463 from rfl, totK_node, tot10462, tot10463]
  decide +kernel

theorem arows10459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10459 = true := by
  rw [show D2M8K2.u10459 = KTree.node D2M8K2.t10464 (nat_lit 22822077) (nat_lit 1532296976) (nat_lit 0) D2M8K2.t10465 from rfl, allE_node, rows10464, irow10459, rows10465]
  all_goals rfl

theorem atot10459 : totK PD2M8K2 D2M8K2.u10459 = [0, 0, 71500428704, 532477428133, 891443843014, 265257265858, 10680993762, 0] := by
  rw [show D2M8K2.u10459 = KTree.node D2M8K2.t10464 (nat_lit 22822077) (nat_lit 1532296976) (nat_lit 0) D2M8K2.t10465 from rfl, totK_node, tot10464, tot10465]
  decide +kernel

theorem arows10460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10460 = true := by
  rw [show D2M8K2.u10460 = KTree.node D2M8K2.t10466 (nat_lit 22823890) (nat_lit 3823450992) (nat_lit 0) D2M8K2.t10467 from rfl, allE_node, rows10466, irow10460, rows10467]
  all_goals rfl

theorem atot10460 : totK PD2M8K2 D2M8K2.u10460 = [0, 0, 344307311699, 879079690258, 505521637456, 65539962862, 2569691499, 0] := by
  rw [show D2M8K2.u10460 = KTree.node D2M8K2.t10466 (nat_lit 22823890) (nat_lit 3823450992) (nat_lit 0) D2M8K2.t10467 from rfl, totK_node, tot10466, tot10467]
  decide +kernel

theorem arows10462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10462 = true := by
  rw [show D2M8K2.u10462 = KTree.node D2M8K2.t10468 (nat_lit 22825393) (nat_lit 1423666189) (nat_lit 0) D2M8K2.t10469 from rfl, allE_node, rows10468, irow10462, rows10469]
  all_goals rfl

theorem atot10462 : totK PD2M8K2 D2M8K2.u10462 = [0, 0, 92722817510, 716860152467, 868868051594, 123744350001, 1096505104, 0] := by
  rw [show D2M8K2.u10462 = KTree.node D2M8K2.t10468 (nat_lit 22825393) (nat_lit 1423666189) (nat_lit 0) D2M8K2.t10469 from rfl, totK_node, tot10468, tot10469]
  decide +kernel

theorem arows10463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10463 = true := by
  rw [show D2M8K2.u10463 = KTree.node D2M8K2.t10470 (nat_lit 22831109) (nat_lit 1577106227) (nat_lit 544) D2M8K2.t10471 from rfl, allE_node, rows10470, irow10463, rows10471]
  all_goals rfl

theorem atot10463 : totK PD2M8K2 D2M8K2.u10463 = [0, 0, 0, 355398781635, 955409909826, 386809125114, 18632570584, 0] := by
  rw [show D2M8K2.u10463 = KTree.node D2M8K2.t10470 (nat_lit 22831109) (nat_lit 1577106227) (nat_lit 544) D2M8K2.t10471 from rfl, totK_node, tot10470, tot10471]
  decide +kernel

theorem arows10466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10466 = true := by
  rw [show D2M8K2.u10466 = KTree.node D2M8K2.t10472 (nat_lit 22833022) (nat_lit 2451555198) (nat_lit 0) D2M8K2.t10473 from rfl, allE_node, rows10472, irow10466, rows10473]
  all_goals rfl

theorem atot10466 : totK PD2M8K2 D2M8K2.u10466 = [0, 0, 0, 177803360098, 791170140531, 654717965717, 80029835018, 1138244013] := by
  rw [show D2M8K2.u10466 = KTree.node D2M8K2.t10472 (nat_lit 22833022) (nat_lit 2451555198) (nat_lit 0) D2M8K2.t10473 from rfl, totK_node, tot10472, tot10473]
  decide +kernel

theorem arows10467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10467 = true := by
  rw [show D2M8K2.u10467 = KTree.node D2M8K2.t10474 (nat_lit 22835263) (nat_lit 2274029694) (nat_lit 0) D2M8K2.t10475 from rfl, allE_node, rows10474, irow10467, rows10475]
  all_goals rfl

theorem atot10467 : totK PD2M8K2 D2M8K2.u10467 = [0, 0, 0, 554101952987, 953454384429, 259025496731, 7053042878, 0] := by
  rw [show D2M8K2.u10467 = KTree.node D2M8K2.t10474 (nat_lit 22835263) (nat_lit 2274029694) (nat_lit 0) D2M8K2.t10475 from rfl, totK_node, tot10474, tot10475]
  decide +kernel

theorem arows10469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10469 = true := by
  rw [show D2M8K2.u10469 = KTree.node D2M8K2.t10476 (nat_lit 22841128) (nat_lit 2146912879) (nat_lit 0) D2M8K2.t10477 from rfl, allE_node, rows10476, irow10469, rows10477]
  all_goals rfl

theorem atot10469 : totK PD2M8K2 D2M8K2.u10469 = [0, 0, 0, 398023221434, 952317673850, 393924655773, 23298057802, 0] := by
  rw [show D2M8K2.u10469 = KTree.node D2M8K2.t10476 (nat_lit 22841128) (nat_lit 2146912879) (nat_lit 0) D2M8K2.t10477 from rfl, totK_node, tot10476, tot10477]
  decide +kernel

theorem arows10470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10470 = true := by
  rw [show D2M8K2.u10470 = KTree.node D2M8K2.t10478 (nat_lit 22844479) (nat_lit 2333953420) (nat_lit 0) D2M8K2.t10479 from rfl, allE_node, rows10478, irow10470, rows10479]
  all_goals rfl

theorem atot10470 : totK PD2M8K2 D2M8K2.u10470 = [0, 0, 0, 369726036695, 930261192632, 399708611155, 22005960557, 0] := by
  rw [show D2M8K2.u10470 = KTree.node D2M8K2.t10478 (nat_lit 22844479) (nat_lit 2333953420) (nat_lit 0) D2M8K2.t10479 from rfl, totK_node, tot10478, tot10479]
  decide +kernel

theorem arows10474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10474 = true := by
  rw [show D2M8K2.u10474 = KTree.node D2M8K2.t10480 (nat_lit 22846000) (nat_lit 3018970499) (nat_lit 0) D2M8K2.t10481 from rfl, allE_node, rows10480, irow10474, rows10481]
  all_goals rfl

theorem atot10474 : totK PD2M8K2 D2M8K2.u10474 = [0, 0, 0, 124494235298, 758538432898, 712566268198, 96556906430, 1095107716] := by
  rw [show D2M8K2.u10474 = KTree.node D2M8K2.t10480 (nat_lit 22846000) (nat_lit 3018970499) (nat_lit 0) D2M8K2.t10481 from rfl, totK_node, tot10480, tot10481]
  decide +kernel

theorem arows10475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10475 = true := by
  rw [show D2M8K2.u10475 = KTree.node D2M8K2.t10482 (nat_lit 22851842) (nat_lit 2926601310) (nat_lit 128) D2M8K2.t10483 from rfl, allE_node, rows10482, irow10475, rows10483]
  all_goals rfl

theorem atot10475 : totK PD2M8K2 D2M8K2.u10475 = [0, 0, 351453791850, 849696581632, 363942762299, 126384346035, 61725179771, 3819176523] := by
  rw [show D2M8K2.u10475 = KTree.node D2M8K2.t10482 (nat_lit 22851842) (nat_lit 2926601310) (nat_lit 128) D2M8K2.t10483 from rfl, totK_node, tot10482, tot10483]
  decide +kernel

theorem arows10477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10477 = true := by
  rw [show D2M8K2.u10477 = KTree.node D2M8K2.t10484 (nat_lit 22853503) (nat_lit 1674736625) (nat_lit 0) D2M8K2.t10485 from rfl, allE_node, rows10484, irow10477, rows10485]
  all_goals rfl

theorem atot10477 : totK PD2M8K2 D2M8K2.u10477 = [0, 0, 147990819149, 709345271752, 816932814674, 123765012641, 1369150432, 0] := by
  rw [show D2M8K2.u10477 = KTree.node D2M8K2.t10484 (nat_lit 22853503) (nat_lit 1674736625) (nat_lit 0) D2M8K2.t10485 from rfl, totK_node, tot10484, tot10485]
  decide +kernel

theorem arows10478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10478 = true := by
  rw [show D2M8K2.u10478 = KTree.node D2M8K2.t10486 (nat_lit 22855568) (nat_lit 3627925257) (nat_lit 0) D2M8K2.t10487 from rfl, allE_node, rows10486, irow10478, rows10487]
  all_goals rfl

theorem atot10478 : totK PD2M8K2 D2M8K2.u10478 = [0, 0, 324884166367, 938598418643, 543168130455, 43266037499, 0, 0] := by
  rw [show D2M8K2.u10478 = KTree.node D2M8K2.t10486 (nat_lit 22855568) (nat_lit 3627925257) (nat_lit 0) D2M8K2.t10487 from rfl, totK_node, tot10486, tot10487]
  decide +kernel

theorem arows10481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10481 = true := by
  rw [show D2M8K2.u10481 = KTree.node D2M8K2.t10488 (nat_lit 22857362) (nat_lit 3946923468) (nat_lit 0) D2M8K2.t10489 from rfl, allE_node, rows10488, irow10481, rows10489]
  all_goals rfl

theorem atot10481 : totK PD2M8K2 D2M8K2.u10481 = [0, 0, 79678872252, 548566917302, 859733040116, 314055768142, 16293883145, 0] := by
  rw [show D2M8K2.u10481 = KTree.node D2M8K2.t10488 (nat_lit 22857362) (nat_lit 3946923468) (nat_lit 0) D2M8K2.t10489 from rfl, totK_node, tot10488, tot10489]
  decide +kernel

theorem arows10482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10482 = true := by
  rw [show D2M8K2.u10482 = KTree.node D2M8K2.t10490 (nat_lit 22859554) (nat_lit 4187750769) (nat_lit 0) D2M8K2.t10491 from rfl, allE_node, rows10490, irow10482, rows10491]
  all_goals rfl

theorem atot10482 : totK PD2M8K2 D2M8K2.u10482 = [0, 0, 417294983749, 963720076851, 429555939552, 33240092574, 0, 0] := by
  rw [show D2M8K2.u10482 = KTree.node D2M8K2.t10490 (nat_lit 22859554) (nat_lit 4187750769) (nat_lit 0) D2M8K2.t10491 from rfl, totK_node, tot10490, tot10491]
  decide +kernel

theorem arows10484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10484 = true := by
  rw [show D2M8K2.u10484 = KTree.node D2M8K2.t10492 (nat_lit 22862754) (nat_lit 2364809656) (nat_lit 0) D2M8K2.t10493 from rfl, allE_node, rows10492, irow10484, rows10493]
  all_goals rfl

theorem atot10484 : totK PD2M8K2 D2M8K2.u10484 = [0, 0, 252896668865, 798042387848, 652561605009, 95116647717, 1198073392, 0] := by
  rw [show D2M8K2.u10484 = KTree.node D2M8K2.t10492 (nat_lit 22862754) (nat_lit 2364809656) (nat_lit 0) D2M8K2.t10493 from rfl, totK_node, tot10492, tot10493]
  decide +kernel

theorem arows10485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10485 = true := by
  rw [show D2M8K2.u10485 = KTree.node D2M8K2.t10494 (nat_lit 22864436) (nat_lit 3583837547) (nat_lit 0) D2M8K2.t10495 from rfl, allE_node, rows10494, irow10485, rows10495]
  all_goals rfl

theorem atot10485 : totK PD2M8K2 D2M8K2.u10485 = [0, 0, 175321203414, 710586991000, 752082546584, 180433278549, 8466643012, 0] := by
  rw [show D2M8K2.u10485 = KTree.node D2M8K2.t10494 (nat_lit 22864436) (nat_lit 3583837547) (nat_lit 0) D2M8K2.t10495 from rfl, totK_node, tot10494, tot10495]
  decide +kernel

theorem arows10493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10493 = true := by
  rw [show D2M8K2.u10493 = KTree.node D2M8K2.t10496 (nat_lit 22869380) (nat_lit 2637165904) (nat_lit 0) D2M8K2.t10497 from rfl, allE_node, rows10496, irow10493, rows10497]
  all_goals rfl

theorem atot10493 : totK PD2M8K2 D2M8K2.u10493 = [0, 0, 265581987306, 836358965883, 638077158535, 82186545858, 1268739303, 0] := by
  rw [show D2M8K2.u10493 = KTree.node D2M8K2.t10496 (nat_lit 22869380) (nat_lit 2637165904) (nat_lit 0) D2M8K2.t10497 from rfl, totK_node, tot10496, tot10497]
  decide +kernel

theorem arows10494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10494 = true := by
  rw [show D2M8K2.u10494 = KTree.node D2M8K2.t10498 (nat_lit 22871209) (nat_lit 1406233981) (nat_lit 0) D2M8K2.t10499 from rfl, allE_node, rows10498, irow10494, rows10499]
  all_goals rfl

theorem atot10494 : totK PD2M8K2 D2M8K2.u10494 = [0, 110047735289, 240876973602, 435721212129, 742947814215, 260925443037, 13069928192, 0] := by
  rw [show D2M8K2.u10494 = KTree.node D2M8K2.t10498 (nat_lit 22871209) (nat_lit 1406233981) (nat_lit 0) D2M8K2.t10499 from rfl, totK_node, tot10498, tot10499]
  decide +kernel

theorem arows10496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10496 = true := by
  rw [show D2M8K2.u10496 = KTree.node D2M8K2.t10500 (nat_lit 22893727) (nat_lit 2274880256) (nat_lit 0) D2M8K2.t10501 from rfl, allE_node, rows10500, irow10496, rows10501]
  all_goals rfl

theorem atot10496 : totK PD2M8K2 D2M8K2.u10496 = [0, 322899444704, 900920332843, 518213616009, 40794606127, 0, 0, 0] := by
  rw [show D2M8K2.u10496 = KTree.node D2M8K2.t10500 (nat_lit 22893727) (nat_lit 2274880256) (nat_lit 0) D2M8K2.t10501 from rfl, totK_node, tot10500, tot10501]
  decide +kernel

theorem arows10497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10497 = true := by
  rw [show D2M8K2.u10497 = KTree.node D2M8K2.t10502 (nat_lit 22895504) (nat_lit 3788156863) (nat_lit 0) D2M8K2.t10503 from rfl, allE_node, rows10502, irow10497, rows10503]
  all_goals rfl

theorem atot10497 : totK PD2M8K2 D2M8K2.u10497 = [0, 140390059244, 706223472566, 811030498194, 142675426909, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10497 = KTree.node D2M8K2.t10502 (nat_lit 22895504) (nat_lit 3788156863) (nat_lit 0) D2M8K2.t10503 from rfl, totK_node, tot10502, tot10503]
  decide +kernel

theorem arows10500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10500 = true := by
  rw [show D2M8K2.u10500 = KTree.node D2M8K2.t10504 (nat_lit 22900848) (nat_lit 3372027654) (nat_lit 0) D2M8K2.t10505 from rfl, allE_node, rows10504, irow10500, rows10505]
  all_goals rfl

theorem atot10500 : totK PD2M8K2 D2M8K2.u10500 = [0, 239415021708, 779471575830, 657787418499, 98242063192, 1164319620, 0, 0] := by
  rw [show D2M8K2.u10500 = KTree.node D2M8K2.t10504 (nat_lit 22900848) (nat_lit 3372027654) (nat_lit 0) D2M8K2.t10505 from rfl, totK_node, tot10504, tot10505]
  decide +kernel

theorem arows10501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10501 = true := by
  rw [show D2M8K2.u10501 = KTree.node D2M8K2.t10506 (nat_lit 22902688) (nat_lit 3756584681) (nat_lit 0) D2M8K2.t10507 from rfl, allE_node, rows10506, irow10501, rows10507]
  all_goals rfl

theorem atot10501 : totK PD2M8K2 D2M8K2.u10501 = [0, 174553003194, 647872482986, 739307777031, 204778748464, 11885407614, 0, 0] := by
  rw [show D2M8K2.u10501 = KTree.node D2M8K2.t10506 (nat_lit 22902688) (nat_lit 3756584681) (nat_lit 0) D2M8K2.t10507 from rfl, totK_node, tot10506, tot10507]
  decide +kernel

theorem arows10503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10503 = true := by
  rw [show D2M8K2.u10503 = KTree.node D2M8K2.t10508 (nat_lit 22904395) (nat_lit 1776847844) (nat_lit 0) D2M8K2.t10509 from rfl, allE_node, rows10508, irow10503, rows10509]
  all_goals rfl

theorem atot10503 : totK PD2M8K2 D2M8K2.u10503 = [0, 239106711706, 791366373402, 664553922492, 105591525606, 1198073392, 0, 0] := by
  rw [show D2M8K2.u10503 = KTree.node D2M8K2.t10508 (nat_lit 22904395) (nat_lit 1776847844) (nat_lit 0) D2M8K2.t10509 from rfl, totK_node, tot10508, tot10509]
  decide +kernel

theorem arows10504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10504 = true := by
  rw [show D2M8K2.u10504 = KTree.node D2M8K2.t10510 (nat_lit 22906110) (nat_lit 3886074501) (nat_lit 0) D2M8K2.t10511 from rfl, allE_node, rows10510, irow10504, rows10511]
  all_goals rfl

theorem atot10504 : totK PD2M8K2 D2M8K2.u10504 = [0, 159329899136, 642970201410, 739511495541, 229235058943, 12052611869, 0, 0] := by
  rw [show D2M8K2.u10504 = KTree.node D2M8K2.t10510 (nat_lit 22906110) (nat_lit 3886074501) (nat_lit 0) D2M8K2.t10511 from rfl, totK_node, tot10510, tot10511]
  decide +kernel

theorem arows10508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10508 = true := by
  rw [show D2M8K2.u10508 = KTree.node D2M8K2.t10512 (nat_lit 22907492) (nat_lit 3309796675) (nat_lit 0) D2M8K2.t10513 from rfl, allE_node, rows10512, irow10508, rows10513]
  all_goals rfl

theorem atot10508 : totK PD2M8K2 D2M8K2.u10508 = [0, 261715479344, 806772619468, 619844238085, 91716878505, 1096505104, 0, 0] := by
  rw [show D2M8K2.u10508 = KTree.node D2M8K2.t10512 (nat_lit 22907492) (nat_lit 3309796675) (nat_lit 0) D2M8K2.t10513 from rfl, totK_node, tot10512, tot10513]
  decide +kernel

theorem arows10509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10509 = true := by
  rw [show D2M8K2.u10509 = KTree.node D2M8K2.t10514 (nat_lit 22909442) (nat_lit 3602028148) (nat_lit 0) D2M8K2.t10515 from rfl, allE_node, rows10514, irow10509, rows10515]
  all_goals rfl

theorem atot10509 : totK PD2M8K2 D2M8K2.u10509 = [0, 202020011335, 744506858882, 709606447703, 136635352852, 3884009855, 0, 0] := by
  rw [show D2M8K2.u10509 = KTree.node D2M8K2.t10514 (nat_lit 22909442) (nat_lit 3602028148) (nat_lit 0) D2M8K2.t10515 from rfl, totK_node, tot10514, tot10515]
  decide +kernel

theorem arows10511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10511 = true := by
  rw [show D2M8K2.u10511 = KTree.node D2M8K2.t10516 (nat_lit 22911657) (nat_lit 1839546635) (nat_lit 0) D2M8K2.t10517 from rfl, allE_node, rows10516, irow10511, rows10517]
  all_goals rfl

theorem atot10511 : totK PD2M8K2 D2M8K2.u10511 = [0, 124442828397, 662482122219, 811957481697, 195960535982, 5011483316, 0, 0] := by
  rw [show D2M8K2.u10511 = KTree.node D2M8K2.t10516 (nat_lit 22911657) (nat_lit 1839546635) (nat_lit 0) D2M8K2.t10517 from rfl, totK_node, tot10516, tot10517]
  decide +kernel

theorem arows10512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10512 = true := by
  rw [show D2M8K2.u10512 = KTree.node D2M8K2.t10518 (nat_lit 22913968) (nat_lit 3441116985) (nat_lit 0) D2M8K2.t10519 from rfl, allE_node, rows10518, irow10512, rows10519]
  all_goals rfl

theorem atot10512 : totK PD2M8K2 D2M8K2.u10512 = [0, 0, 383250912747, 936455566179, 411485665631, 27007146182, 0, 0] := by
  rw [show D2M8K2.u10512 = KTree.node D2M8K2.t10518 (nat_lit 22913968) (nat_lit 3441116985) (nat_lit 0) D2M8K2.t10519 from rfl, totK_node, tot10518, tot10519]
  decide +kernel

theorem arows10515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10515 = true := by
  rw [show D2M8K2.u10515 = KTree.node D2M8K2.t10520 (nat_lit 22915170) (nat_lit 2751591944) (nat_lit 0) D2M8K2.t10521 from rfl, allE_node, rows10520, irow10515, rows10521]
  all_goals rfl

theorem atot10515 : totK PD2M8K2 D2M8K2.u10515 = [0, 0, 85808503149, 730581223119, 773190786554, 121986800058, 1369150432, 0] := by
  rw [show D2M8K2.u10515 = KTree.node D2M8K2.t10520 (nat_lit 22915170) (nat_lit 2751591944) (nat_lit 0) D2M8K2.t10521 from rfl, totK_node, tot10520, tot10521]
  decide +kernel

theorem arows10516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10516 = true := by
  rw [show D2M8K2.u10516 = KTree.node D2M8K2.t10522 (nat_lit 22920911) (nat_lit 2429828136) (nat_lit 128) D2M8K2.t10523 from rfl, allE_node, rows10522, irow10516, rows10523]
  all_goals rfl

theorem atot10516 : totK PD2M8K2 D2M8K2.u10516 = [0, 0, 378991628482, 955314936980, 403142679357, 19886856612, 0, 0] := by
  rw [show D2M8K2.u10516 = KTree.node D2M8K2.t10522 (nat_lit 22920911) (nat_lit 2429828136) (nat_lit 128) D2M8K2.t10523 from rfl, totK_node, tot10522, tot10523]
  decide +kernel

theorem arows10518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10518 = true := by
  rw [show D2M8K2.u10518 = KTree.node D2M8K2.t10524 (nat_lit 22924614) (nat_lit 3892297328) (nat_lit 0) D2M8K2.t10525 from rfl, allE_node, rows10524, irow10518, rows10525]
  all_goals rfl

theorem atot10518 : totK PD2M8K2 D2M8K2.u10518 = [0, 0, 412830176611, 962738551845, 407726363127, 17835779084, 0, 0] := by
  rw [show D2M8K2.u10518 = KTree.node D2M8K2.t10524 (nat_lit 22924614) (nat_lit 3892297328) (nat_lit 0) D2M8K2.t10525 from rfl, totK_node, tot10524, tot10525]
  decide +kernel

theorem arows10519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10519 = true := by
  rw [show D2M8K2.u10519 = KTree.node D2M8K2.t10526 (nat_lit 22927640) (nat_lit 3895160028) (nat_lit 0) D2M8K2.t10527 from rfl, allE_node, rows10526, irow10519, rows10527]
  all_goals rfl

theorem atot10519 : totK PD2M8K2 D2M8K2.u10519 = [0, 0, 335843686243, 920106564637, 465197589515, 28443192514, 0, 0] := by
  rw [show D2M8K2.u10519 = KTree.node D2M8K2.t10526 (nat_lit 22927640) (nat_lit 3895160028) (nat_lit 0) D2M8K2.t10527 from rfl, totK_node, tot10526, tot10527]
  decide +kernel

theorem arows10524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10524 = true := by
  rw [show D2M8K2.u10524 = KTree.node D2M8K2.t10528 (nat_lit 22931232) (nat_lit 3428437145) (nat_lit 0) D2M8K2.t10529 from rfl, allE_node, rows10528, irow10524, rows10529]
  all_goals rfl

theorem atot10524 : totK PD2M8K2 D2M8K2.u10524 = [0, 0, 409764881071, 991844219453, 390677285790, 11568577828, 0, 0] := by
  rw [show D2M8K2.u10524 = KTree.node D2M8K2.t10528 (nat_lit 22931232) (nat_lit 3428437145) (nat_lit 0) D2M8K2.t10529 from rfl, totK_node, tot10528, tot10529]
  decide +kernel

theorem arows10525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10525 = true := by
  rw [show D2M8K2.u10525 = KTree.node D2M8K2.t10530 (nat_lit 22938196) (nat_lit 3739343447) (nat_lit 0) D2M8K2.t10531 from rfl, allE_node, rows10530, irow10525, rows10531]
  all_goals rfl

theorem atot10525 : totK PD2M8K2 D2M8K2.u10525 = [0, 357337161097, 847311518946, 516323392245, 106444763530, 7840298456, 0, 0] := by
  rw [show D2M8K2.u10525 = KTree.node D2M8K2.t10530 (nat_lit 22938196) (nat_lit 3739343447) (nat_lit 0) D2M8K2.t10531 from rfl, totK_node, tot10530, tot10531]
  decide +kernel

theorem arows10527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10527 = true := by
  rw [show D2M8K2.u10527 = KTree.node D2M8K2.t10532 (nat_lit 22939691) (nat_lit 2570159007) (nat_lit 0) D2M8K2.t10533 from rfl, allE_node, rows10532, irow10527, rows10533]
  all_goals rfl

theorem atot10527 : totK PD2M8K2 D2M8K2.u10527 = [0, 84943629437, 553258554295, 829264026933, 336113509915, 25373788367, 0, 0] := by
  rw [show D2M8K2.u10527 = KTree.node D2M8K2.t10532 (nat_lit 22939691) (nat_lit 2570159007) (nat_lit 0) D2M8K2.t10533 from rfl, totK_node, tot10532, tot10533]
  decide +kernel

theorem arows10528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10528 = true := by
  rw [show D2M8K2.u10528 = KTree.node D2M8K2.t10534 (nat_lit 22940934) (nat_lit 2799965955) (nat_lit 0) D2M8K2.t10535 from rfl, allE_node, rows10534, irow10528, rows10535]
  all_goals rfl

theorem atot10528 : totK PD2M8K2 D2M8K2.u10528 = [0, 213811174585, 635661830649, 702872920585, 256837922323, 10460337654, 0, 0] := by
  rw [show D2M8K2.u10528 = KTree.node D2M8K2.t10534 (nat_lit 22940934) (nat_lit 2799965955) (nat_lit 0) D2M8K2.t10535 from rfl, totK_node, tot10534, tot10535]
  decide +kernel

theorem arows10531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10531 = true := by
  rw [show D2M8K2.u10531 = KTree.node D2M8K2.t10536 (nat_lit 22942563) (nat_lit 3481550644) (nat_lit 0) D2M8K2.t10537 from rfl, allE_node, rows10536, irow10531, rows10537]
  all_goals rfl

theorem atot10531 : totK PD2M8K2 D2M8K2.u10531 = [0, 170040538896, 753093420099, 731926603744, 146194282712, 6972471598, 0, 0] := by
  rw [show D2M8K2.u10531 = KTree.node D2M8K2.t10536 (nat_lit 22942563) (nat_lit 3481550644) (nat_lit 0) D2M8K2.t10537 from rfl, totK_node, tot10536, tot10537]
  decide +kernel

theorem arows10532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10532 = true := by
  rw [show D2M8K2.u10532 = KTree.node D2M8K2.t10538 (nat_lit 22944654) (nat_lit 3828698869) (nat_lit 0) D2M8K2.t10539 from rfl, allE_node, rows10538, irow10532, rows10539]
  all_goals rfl

theorem atot10532 : totK PD2M8K2 D2M8K2.u10532 = [0, 249485573521, 774764767068, 664594947413, 132332897754, 4900554076, 0, 0] := by
  rw [show D2M8K2.u10532 = KTree.node D2M8K2.t10538 (nat_lit 22944654) (nat_lit 3828698869) (nat_lit 0) D2M8K2.t10539 from rfl, totK_node, tot10538, tot10539]
  decide +kernel

theorem arows10534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10534 = true := by
  rw [show D2M8K2.u10534 = KTree.node D2M8K2.t10540 (nat_lit 22946123) (nat_lit 2738926159) (nat_lit 0) D2M8K2.t10541 from rfl, allE_node, rows10540, irow10534, rows10541]
  all_goals rfl

theorem atot10534 : totK PD2M8K2 D2M8K2.u10534 = [0, 166907483503, 696080128174, 757771541641, 183394978656, 7229436959, 0, 0] := by
  rw [show D2M8K2.u10534 = KTree.node D2M8K2.t10540 (nat_lit 22946123) (nat_lit 2738926159) (nat_lit 0) D2M8K2.t10541 from rfl, totK_node, tot10540, tot10541]
  decide +kernel

theorem arows10535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10535 = true := by
  rw [show D2M8K2.u10535 = KTree.node D2M8K2.t10542 (nat_lit 22947992) (nat_lit 3522529939) (nat_lit 0) D2M8K2.t10543 from rfl, allE_node, rows10542, irow10535, rows10543]
  all_goals rfl

theorem atot10535 : totK PD2M8K2 D2M8K2.u10535 = [0, 244493969582, 736622308997, 657494692059, 154201408297, 6008233017, 0, 0] := by
  rw [show D2M8K2.u10535 = KTree.node D2M8K2.t10542 (nat_lit 22947992) (nat_lit 3522529939) (nat_lit 0) D2M8K2.t10543 from rfl, totK_node, tot10542, tot10543]
  decide +kernel

theorem arows10539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10539 = true := by
  rw [show D2M8K2.u10539 = KTree.node D2M8K2.t10544 (nat_lit 22949189) (nat_lit 2348817020) (nat_lit 0) D2M8K2.t10545 from rfl, allE_node, rows10544, irow10539, rows10545]
  all_goals rfl

theorem atot10539 : totK PD2M8K2 D2M8K2.u10539 = [0, 178048372752, 766318781415, 741158610471, 113201664313, 1096156699, 0, 0] := by
  rw [show D2M8K2.u10539 = KTree.node D2M8K2.t10544 (nat_lit 22949189) (nat_lit 2348817020) (nat_lit 0) D2M8K2.t10545 from rfl, totK_node, tot10544, tot10545]
  decide +kernel

theorem arows10540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10540 = true := by
  rw [show D2M8K2.u10540 = KTree.node D2M8K2.t10546 (nat_lit 22951769) (nat_lit 1697010133) (nat_lit 0) D2M8K2.t10547 from rfl, allE_node, rows10546, irow10540, rows10547]
  all_goals rfl

theorem atot10540 : totK PD2M8K2 D2M8K2.u10540 = [0, 244236898341, 771198032612, 691057789296, 138294995415, 3880716147, 0, 0] := by
  rw [show D2M8K2.u10540 = KTree.node D2M8K2.t10546 (nat_lit 22951769) (nat_lit 1697010133) (nat_lit 0) D2M8K2.t10547 from rfl, totK_node, tot10546, tot10547]
  decide +kernel

theorem arows10542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10542 = true := by
  rw [show D2M8K2.u10542 = KTree.node D2M8K2.t10548 (nat_lit 22953722) (nat_lit 4026929500) (nat_lit 0) D2M8K2.t10549 from rfl, allE_node, rows10548, irow10542, rows10549]
  all_goals rfl

theorem atot10542 : totK PD2M8K2 D2M8K2.u10542 = [0, 88830982688, 582656145213, 878257244183, 263757187778, 7615388454, 0, 0] := by
  rw [show D2M8K2.u10542 = KTree.node D2M8K2.t10548 (nat_lit 22953722) (nat_lit 4026929500) (nat_lit 0) D2M8K2.t10549 from rfl, totK_node, tot10548, tot10549]
  decide +kernel

theorem arows10543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10543 = true := by
  rw [show D2M8K2.u10543 = KTree.node D2M8K2.t10550 (nat_lit 22958960) (nat_lit 3670958530) (nat_lit 0) D2M8K2.t10551 from rfl, allE_node, rows10550, irow10543, rows10551]
  all_goals rfl

theorem atot10543 : totK PD2M8K2 D2M8K2.u10543 = [0, 0, 356565808175, 915927814802, 515276695918, 44383529241, 0, 0] := by
  rw [show D2M8K2.u10543 = KTree.node D2M8K2.t10550 (nat_lit 22958960) (nat_lit 3670958530) (nat_lit 0) D2M8K2.t10551 from rfl, totK_node, tot10550, tot10551]
  decide +kernel

theorem arows10546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10546 = true := by
  rw [show D2M8K2.u10546 = KTree.node D2M8K2.t10552 (nat_lit 22960471) (nat_lit 2179194564) (nat_lit 0) D2M8K2.t10553 from rfl, allE_node, rows10552, irow10546, rows10553]
  all_goals rfl

theorem atot10546 : totK PD2M8K2 D2M8K2.u10546 = [0, 0, 84661032308, 595978458588, 860501629694, 270293529632, 13824381170, 0] := by
  rw [show D2M8K2.u10546 = KTree.node D2M8K2.t10552 (nat_lit 22960471) (nat_lit 2179194564) (nat_lit 0) D2M8K2.t10553 from rfl, totK_node, tot10552, tot10553]
  decide +kernel

theorem arows10547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10547 = true := by
  rw [show D2M8K2.u10547 = KTree.node D2M8K2.t10554 (nat_lit 22962165) (nat_lit 1127558416) (nat_lit 0) D2M8K2.t10555 from rfl, allE_node, rows10554, irow10547, rows10555]
  all_goals rfl

theorem atot10547 : totK PD2M8K2 D2M8K2.u10547 = [0, 0, 315702768085, 837630106201, 544754340975, 97486702504, 1353333895, 0] := by
  rw [show D2M8K2.u10547 = KTree.node D2M8K2.t10554 (nat_lit 22962165) (nat_lit 1127558416) (nat_lit 0) D2M8K2.t10555 from rfl, totK_node, tot10554, tot10555]
  decide +kernel

theorem arows10549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10549 = true := by
  rw [show D2M8K2.u10549 = KTree.node D2M8K2.t10556 (nat_lit 22965508) (nat_lit 3478710767) (nat_lit 0) D2M8K2.t10557 from rfl, allE_node, rows10556, irow10549, rows10557]
  all_goals rfl

theorem atot10549 : totK PD2M8K2 D2M8K2.u10549 = [0, 0, 364546245590, 925995013604, 510038149653, 41614432265, 0, 0] := by
  rw [show D2M8K2.u10549 = KTree.node D2M8K2.t10556 (nat_lit 22965508) (nat_lit 3478710767) (nat_lit 0) D2M8K2.t10557 from rfl, totK_node, tot10556, tot10557]
  decide +kernel

theorem arows10550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10550 = true := by
  rw [show D2M8K2.u10550 = KTree.node D2M8K2.t10558 (nat_lit 22967186) (nat_lit 4095256117) (nat_lit 0) D2M8K2.t10559 from rfl, allE_node, rows10558, irow10550, rows10559]
  all_goals rfl

theorem atot10550 : totK PD2M8K2 D2M8K2.u10550 = [0, 0, 118073845999, 692754797333, 820864421290, 162872961023, 4031931762, 0] := by
  rw [show D2M8K2.u10550 = KTree.node D2M8K2.t10558 (nat_lit 22967186) (nat_lit 4095256117) (nat_lit 0) D2M8K2.t10559 from rfl, totK_node, tot10558, tot10559]
  decide +kernel

theorem arows10556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10556 = true := by
  rw [show D2M8K2.u10556 = KTree.node D2M8K2.t10560 (nat_lit 22969065) (nat_lit 1815847795) (nat_lit 0) D2M8K2.t10561 from rfl, allE_node, rows10560, irow10556, rows10561]
  all_goals rfl

theorem atot10556 : totK PD2M8K2 D2M8K2.u10556 = [0, 0, 329466426294, 863618055161, 529657711025, 73819477442, 1186940923, 0] := by
  rw [show D2M8K2.u10556 = KTree.node D2M8K2.t10560 (nat_lit 22969065) (nat_lit 1815847795) (nat_lit 0) D2M8K2.t10561 from rfl, totK_node, tot10560, tot10561]
  decide +kernel

theorem arows10557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10557 = true := by
  rw [show D2M8K2.u10557 = KTree.node D2M8K2.t10562 (nat_lit 22970692) (nat_lit 3777235321) (nat_lit 0) D2M8K2.t10563 from rfl, allE_node, rows10562, irow10557, rows10563]
  all_goals rfl

theorem atot10557 : totK PD2M8K2 D2M8K2.u10557 = [0, 0, 91681601894, 698015555493, 873014263870, 137187347586, 0, 0] := by
  rw [show D2M8K2.u10557 = KTree.node D2M8K2.t10562 (nat_lit 22970692) (nat_lit 3777235321) (nat_lit 0) D2M8K2.t10563 from rfl, totK_node, tot10562, tot10563]
  decide +kernel

theorem arows10559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10559 = true := by
  rw [show D2M8K2.u10559 = KTree.node D2M8K2.t10564 (nat_lit 22972938) (nat_lit 3898492010) (nat_lit 0) D2M8K2.t10565 from rfl, allE_node, rows10564, irow10559, rows10565]
  all_goals rfl

theorem atot10559 : totK PD2M8K2 D2M8K2.u10559 = [0, 43028644854, 392271625609, 864307090779, 506503424784, 48362935054, 1415142070, 0] := by
  rw [show D2M8K2.u10559 = KTree.node D2M8K2.t10564 (nat_lit 22972938) (nat_lit 3898492010) (nat_lit 0) D2M8K2.t10565 from rfl, totK_node, tot10564, tot10565]
  decide +kernel

theorem arows10560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10560 = true := by
  rw [show D2M8K2.u10560 = KTree.node D2M8K2.t10566 (nat_lit 22976485) (nat_lit 1354391865) (nat_lit 0) D2M8K2.t10567 from rfl, allE_node, rows10566, irow10560, rows10567]
  all_goals rfl

theorem atot10560 : totK PD2M8K2 D2M8K2.u10560 = [0, 348473233395, 932030137448, 458012148580, 26282942799, 0, 0, 0] := by
  rw [show D2M8K2.u10560 = KTree.node D2M8K2.t10566 (nat_lit 22976485) (nat_lit 1354391865) (nat_lit 0) D2M8K2.t10567 from rfl, totK_node, tot10566, tot10567]
  decide +kernel

theorem arows10563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10563 = true := by
  rw [show D2M8K2.u10563 = KTree.node D2M8K2.t10568 (nat_lit 22978406) (nat_lit 3816422586) (nat_lit 0) D2M8K2.t10569 from rfl, allE_node, rows10568, irow10563, rows10569]
  all_goals rfl

theorem atot10563 : totK PD2M8K2 D2M8K2.u10563 = [0, 118279383133, 666959944290, 875237134714, 148539753176, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10563 = KTree.node D2M8K2.t10568 (nat_lit 22978406) (nat_lit 3816422586) (nat_lit 0) D2M8K2.t10569 from rfl, totK_node, tot10568, tot10569]
  decide +kernel

theorem arows10564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10564 = true := by
  rw [show D2M8K2.u10564 = KTree.node D2M8K2.t10570 (nat_lit 22980181) (nat_lit 1050457451) (nat_lit 0) D2M8K2.t10571 from rfl, allE_node, rows10570, irow10564, rows10571]
  all_goals rfl

theorem atot10564 : totK PD2M8K2 D2M8K2.u10564 = [0, 285127422974, 874871667825, 584602570916, 83649892749, 5921339170, 0, 0] := by
  rw [show D2M8K2.u10564 = KTree.node D2M8K2.t10570 (nat_lit 22980181) (nat_lit 1050457451) (nat_lit 0) D2M8K2.t10571 from rfl, totK_node, tot10570, tot10571]
  decide +kernel

theorem arows10566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10566 = true := by
  rw [show D2M8K2.u10566 = KTree.node D2M8K2.t10572 (nat_lit 22981904) (nat_lit 3775691661) (nat_lit 0) D2M8K2.t10573 from rfl, allE_node, rows10572, irow10566, rows10573]
  all_goals rfl

theorem atot10566 : totK PD2M8K2 D2M8K2.u10566 = [0, 122840566998, 574186393244, 824948717670, 291568974444, 9396957438, 0, 0] := by
  rw [show D2M8K2.u10566 = KTree.node D2M8K2.t10572 (nat_lit 22981904) (nat_lit 3775691661) (nat_lit 0) D2M8K2.t10573 from rfl, totK_node, tot10572, tot10573]
  decide +kernel

theorem arows10567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10567 = true := by
  rw [show D2M8K2.u10567 = KTree.node D2M8K2.t10574 (nat_lit 22983580) (nat_lit 3869945590) (nat_lit 0) D2M8K2.t10575 from rfl, allE_node, rows10574, irow10567, rows10575]
  all_goals rfl

theorem atot10567 : totK PD2M8K2 D2M8K2.u10567 = [0, 302945896049, 894395194588, 570987327783, 51579238698, 0, 0, 0] := by
  rw [show D2M8K2.u10567 = KTree.node D2M8K2.t10574 (nat_lit 22983580) (nat_lit 3869945590) (nat_lit 0) D2M8K2.t10575 from rfl, totK_node, tot10574, tot10575]
  decide +kernel

theorem arows10571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10571 = true := by
  rw [show D2M8K2.u10571 = KTree.node D2M8K2.t10576 (nat_lit 22985291) (nat_lit 2082816059) (nat_lit 0) D2M8K2.t10577 from rfl, allE_node, rows10576, irow10571, rows10577]
  all_goals rfl

theorem atot10571 : totK PD2M8K2 D2M8K2.u10571 = [0, 83813933705, 536232629753, 867117890976, 276620481301, 13049727234, 0, 0] := by
  rw [show D2M8K2.u10571 = KTree.node D2M8K2.t10576 (nat_lit 22985291) (nat_lit 2082816059) (nat_lit 0) D2M8K2.t10577 from rfl, totK_node, tot10576, tot10577]
  decide +kernel

theorem arows10572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10572 = true := by
  rw [show D2M8K2.u10572 = KTree.node D2M8K2.t10578 (nat_lit 22990102) (nat_lit 2962471475) (nat_lit 0) D2M8K2.t10579 from rfl, allE_node, rows10578, irow10572, rows10579]
  all_goals rfl

theorem atot10572 : totK PD2M8K2 D2M8K2.u10572 = [0, 339473134813, 918199320140, 516087529036, 42439193055, 0, 0, 0] := by
  rw [show D2M8K2.u10572 = KTree.node D2M8K2.t10578 (nat_lit 22990102) (nat_lit 2962471475) (nat_lit 0) D2M8K2.t10579 from rfl, totK_node, tot10578, tot10579]
  decide +kernel

theorem arows10574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10574 = true := by
  rw [show D2M8K2.u10574 = KTree.node D2M8K2.t10580 (nat_lit 22991982) (nat_lit 4042812513) (nat_lit 0) D2M8K2.t10581 from rfl, allE_node, rows10580, irow10574, rows10581]
  all_goals rfl

theorem atot10574 : totK PD2M8K2 D2M8K2.u10574 = [0, 0, 489084745894, 1014728507951, 276670885308, 6350335412, 0, 0] := by
  rw [show D2M8K2.u10574 = KTree.node D2M8K2.t10580 (nat_lit 22991982) (nat_lit 4042812513) (nat_lit 0) D2M8K2.t10581 from rfl, totK_node, tot10580, tot10581]
  decide +kernel

theorem arows10575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10575 = true := by
  rw [show D2M8K2.u10575 = KTree.node D2M8K2.t10582 (nat_lit 22997457) (nat_lit 1843047959) (nat_lit 0) D2M8K2.t10583 from rfl, allE_node, rows10582, irow10575, rows10583]
  all_goals rfl

theorem atot10575 : totK PD2M8K2 D2M8K2.u10575 = [0, 0, 304309414761, 849703663259, 505563055298, 58762328020, 1206465782, 0] := by
  rw [show D2M8K2.u10575 = KTree.node D2M8K2.t10582 (nat_lit 22997457) (nat_lit 1843047959) (nat_lit 0) D2M8K2.t10583 from rfl, totK_node, tot10582, tot10583]
  decide +kernel

theorem arows10578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10578 = true := by
  rw [show D2M8K2.u10578 = KTree.node D2M8K2.t10584 (nat_lit 23000093) (nat_lit 2250294179) (nat_lit 0) D2M8K2.t10585 from rfl, allE_node, rows10584, irow10578, rows10585]
  all_goals rfl

theorem atot10578 : totK PD2M8K2 D2M8K2.u10578 = [0, 0, 249381387768, 871440092860, 626164481084, 53057239737, 0, 0] := by
  rw [show D2M8K2.u10578 = KTree.node D2M8K2.t10584 (nat_lit 23000093) (nat_lit 2250294179) (nat_lit 0) D2M8K2.t10585 from rfl, totK_node, tot10584, tot10585]
  decide +kernel

theorem arows10579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10579 = true := by
  rw [show D2M8K2.u10579 = KTree.node D2M8K2.t10586 (nat_lit 23003142) (nat_lit 3393790581) (nat_lit 0) D2M8K2.t10587 from rfl, allE_node, rows10586, irow10579, rows10587]
  all_goals rfl

theorem atot10579 : totK PD2M8K2 D2M8K2.u10579 = [0, 0, 364638329521, 953431747729, 464790669323, 25461494267, 0, 0] := by
  rw [show D2M8K2.u10579 = KTree.node D2M8K2.t10586 (nat_lit 23003142) (nat_lit 3393790581) (nat_lit 0) D2M8K2.t10587 from rfl, totK_node, tot10586, tot10587]
  decide +kernel

theorem arows10581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10581 = true := by
  rw [show D2M8K2.u10581 = KTree.node D2M8K2.t10588 (nat_lit 23004637) (nat_lit 1209542005) (nat_lit 0) D2M8K2.t10589 from rfl, allE_node, rows10588, irow10581, rows10589]
  all_goals rfl

theorem atot10581 : totK PD2M8K2 D2M8K2.u10581 = [0, 0, 385675602946, 960478879534, 417951680433, 22813051154, 0, 0] := by
  rw [show D2M8K2.u10581 = KTree.node D2M8K2.t10588 (nat_lit 23004637) (nat_lit 1209542005) (nat_lit 0) D2M8K2.t10589 from rfl, totK_node, tot10588, tot10589]
  decide +kernel

theorem arows10582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10582 = true := by
  rw [show D2M8K2.u10582 = KTree.node D2M8K2.t10590 (nat_lit 23011165) (nat_lit 1018709249) (nat_lit 0) D2M8K2.t10591 from rfl, allE_node, rows10590, irow10582, rows10591]
  all_goals rfl

theorem atot10582 : totK PD2M8K2 D2M8K2.u10582 = [0, 0, 250618406545, 820972182487, 594408320054, 74260694512, 1021600638, 0] := by
  rw [show D2M8K2.u10582 = KTree.node D2M8K2.t10590 (nat_lit 23011165) (nat_lit 1018709249) (nat_lit 0) D2M8K2.t10591 from rfl, totK_node, tot10590, tot10591]
  decide +kernel

theorem arows10587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10587 = true := by
  rw [show D2M8K2.u10587 = KTree.node D2M8K2.t10592 (nat_lit 23017017) (nat_lit 1801523931) (nat_lit 0) D2M8K2.t10593 from rfl, allE_node, rows10592, irow10587, rows10593]
  all_goals rfl

theorem atot10587 : totK PD2M8K2 D2M8K2.u10587 = [0, 238966391009, 509240156029, 470964199157, 424701318669, 91945885786, 3552795014, 0] := by
  rw [show D2M8K2.u10587 = KTree.node D2M8K2.t10592 (nat_lit 23017017) (nat_lit 1801523931) (nat_lit 0) D2M8K2.t10593 from rfl, totK_node, tot10592, tot10593]
  decide +kernel

theorem arows10588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10588 = true := by
  rw [show D2M8K2.u10588 = KTree.node D2M8K2.t10594 (nat_lit 23018570) (nat_lit 3960415095) (nat_lit 0) D2M8K2.t10595 from rfl, allE_node, rows10594, irow10588, rows10595]
  all_goals rfl

theorem atot10588 : totK PD2M8K2 D2M8K2.u10588 = [0, 164210109155, 749039232078, 739070234052, 120588618762, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10588 = KTree.node D2M8K2.t10594 (nat_lit 23018570) (nat_lit 3960415095) (nat_lit 0) D2M8K2.t10595 from rfl, totK_node, tot10594, tot10595]
  decide +kernel

theorem arows10590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10590 = true := by
  rw [show D2M8K2.u10590 = KTree.node D2M8K2.t10596 (nat_lit 23020939) (nat_lit 1742990493) (nat_lit 0) D2M8K2.t10597 from rfl, allE_node, rows10596, irow10590, rows10597]
  all_goals rfl

theorem atot10590 : totK PD2M8K2 D2M8K2.u10590 = [0, 264133658271, 833132371748, 668829622825, 74071853700, 0, 0, 0] := by
  rw [show D2M8K2.u10590 = KTree.node D2M8K2.t10596 (nat_lit 23020939) (nat_lit 1742990493) (nat_lit 0) D2M8K2.t10597 from rfl, totK_node, tot10596, tot10597]
  decide +kernel

theorem arows10591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10591 = true := by
  rw [show D2M8K2.u10591 = KTree.node D2M8K2.t10598 (nat_lit 23022494) (nat_lit 3941475544) (nat_lit 0) D2M8K2.t10599 from rfl, allE_node, rows10598, irow10591, rows10599]
  all_goals rfl

theorem atot10591 : totK PD2M8K2 D2M8K2.u10591 = [0, 154431426411, 641778453997, 722841106572, 282588159348, 25111632603, 0, 0] := by
  rw [show D2M8K2.u10591 = KTree.node D2M8K2.t10598 (nat_lit 23022494) (nat_lit 3941475544) (nat_lit 0) D2M8K2.t10599 from rfl, totK_node, tot10598, tot10599]
  decide +kernel

theorem arows10594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10594 = true := by
  rw [show D2M8K2.u10594 = KTree.node D2M8K2.t10600 (nat_lit 23023758) (nat_lit 3722186984) (nat_lit 0) D2M8K2.t10601 from rfl, allE_node, rows10600, irow10594, rows10601]
  all_goals rfl

theorem atot10594 : totK PD2M8K2 D2M8K2.u10594 = [0, 175298174919, 606708841962, 739153435929, 289163946541, 10788280093, 0, 0] := by
  rw [show D2M8K2.u10594 = KTree.node D2M8K2.t10600 (nat_lit 23023758) (nat_lit 3722186984) (nat_lit 0) D2M8K2.t10601 from rfl, totK_node, tot10600, tot10601]
  decide +kernel

theorem arows10595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10595 = true := by
  rw [show D2M8K2.u10595 = KTree.node D2M8K2.t10602 (nat_lit 23028677) (nat_lit 2065959126) (nat_lit 0) D2M8K2.t10603 from rfl, allE_node, rows10602, irow10595, rows10603]
  all_goals rfl

theorem atot10595 : totK PD2M8K2 D2M8K2.u10595 = [0, 265889318645, 809931689722, 642658906192, 95945544270, 1198073392, 0, 0] := by
  rw [show D2M8K2.u10595 = KTree.node D2M8K2.t10602 (nat_lit 23028677) (nat_lit 2065959126) (nat_lit 0) D2M8K2.t10603 from rfl, totK_node, tot10602, tot10603]
  decide +kernel

theorem arows10597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10597 = true := by
  rw [show D2M8K2.u10597 = KTree.node D2M8K2.t10604 (nat_lit 23030320) (nat_lit 3117454045) (nat_lit 0) D2M8K2.t10605 from rfl, allE_node, rows10604, irow10597, rows10605]
  all_goals rfl

theorem atot10597 : totK PD2M8K2 D2M8K2.u10597 = [0, 121024145981, 614368307177, 810243441743, 241472478862, 12052611869, 0, 0] := by
  rw [show D2M8K2.u10597 = KTree.node D2M8K2.t10604 (nat_lit 23030320) (nat_lit 3117454045) (nat_lit 0) D2M8K2.t10605 from rfl, totK_node, tot10604, tot10605]
  decide +kernel

theorem arows10598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10598 = true := by
  rw [show D2M8K2.u10598 = KTree.node D2M8K2.t10606 (nat_lit 23031742) (nat_lit 3692370633) (nat_lit 0) D2M8K2.t10607 from rfl, allE_node, rows10606, irow10598, rows10607]
  all_goals rfl

theorem atot10598 : totK PD2M8K2 D2M8K2.u10598 = [0, 303079282579, 880380191611, 573929561644, 54996222518, 0, 0, 0] := by
  rw [show D2M8K2.u10598 = KTree.node D2M8K2.t10606 (nat_lit 23031742) (nat_lit 3692370633) (nat_lit 0) D2M8K2.t10607 from rfl, totK_node, tot10606, tot10607]
  decide +kernel

theorem arows10602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10602 = true := by
  rw [show D2M8K2.u10602 = KTree.node D2M8K2.t10608 (nat_lit 23033697) (nat_lit 1858652781) (nat_lit 0) D2M8K2.t10609 from rfl, allE_node, rows10608, irow10602, rows10609]
  all_goals rfl

theorem atot10602 : totK PD2M8K2 D2M8K2.u10602 = [0, 148509923255, 659324834163, 801130331853, 191067678196, 4980514959, 0, 0] := by
  rw [show D2M8K2.u10602 = KTree.node D2M8K2.t10608 (nat_lit 23033697) (nat_lit 1858652781) (nat_lit 0) D2M8K2.t10609 from rfl, totK_node, tot10608, tot10609]
  decide +kernel

theorem arows10603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10603 = true := by
  rw [show D2M8K2.u10603 = KTree.node D2M8K2.t10610 (nat_lit 23035771) (nat_lit 2224952177) (nat_lit 0) D2M8K2.t10611 from rfl, allE_node, rows10610, irow10603, rows10611]
  all_goals rfl

theorem atot10603 : totK PD2M8K2 D2M8K2.u10603 = [0, 197215485410, 758355369889, 741754946461, 129403370961, 1268739303, 0, 0] := by
  rw [show D2M8K2.u10603 = KTree.node D2M8K2.t10610 (nat_lit 23035771) (nat_lit 2224952177) (nat_lit 0) D2M8K2.t10611 from rfl, totK_node, tot10610, tot10611]
  decide +kernel

theorem arows10605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10605 = true := by
  rw [show D2M8K2.u10605 = KTree.node D2M8K2.t10612 (nat_lit 23037756) (nat_lit 3255558676) (nat_lit 0) D2M8K2.t10613 from rfl, allE_node, rows10612, irow10605, rows10613]
  all_goals rfl

theorem atot10605 : totK PD2M8K2 D2M8K2.u10605 = [0, 0, 402077184286, 971826424919, 383202326189, 17771419585, 0, 0] := by
  rw [show D2M8K2.u10605 = KTree.node D2M8K2.t10612 (nat_lit 23037756) (nat_lit 3255558676) (nat_lit 0) D2M8K2.t10613 from rfl, totK_node, tot10612, tot10613]
  decide +kernel

theorem arows10606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10606 = true := by
  rw [show D2M8K2.u10606 = KTree.node D2M8K2.t10614 (nat_lit 23039360) (nat_lit 2732752161) (nat_lit 0) D2M8K2.t10615 from rfl, allE_node, rows10614, irow10606, rows10615]
  all_goals rfl

theorem atot10606 : totK PD2M8K2 D2M8K2.u10606 = [0, 0, 163374322970, 741271584261, 723152927746, 101630344405, 1239866073, 0] := by
  rw [show D2M8K2.u10606 = KTree.node D2M8K2.t10614 (nat_lit 23039360) (nat_lit 2732752161) (nat_lit 0) D2M8K2.t10615 from rfl, totK_node, tot10614, tot10615]
  decide +kernel

theorem arows10609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10609 = true := by
  rw [show D2M8K2.u10609 = KTree.node D2M8K2.t10616 (nat_lit 23041773) (nat_lit 1468512627) (nat_lit 0) D2M8K2.t10617 from rfl, allE_node, rows10616, irow10609, rows10617]
  all_goals rfl

theorem atot10609 : totK PD2M8K2 D2M8K2.u10609 = [0, 0, 324554878658, 886445536580, 566042076602, 50559635189, 0, 0] := by
  rw [show D2M8K2.u10609 = KTree.node D2M8K2.t10616 (nat_lit 23041773) (nat_lit 1468512627) (nat_lit 0) D2M8K2.t10617 from rfl, totK_node, tot10616, tot10617]
  decide +kernel

theorem arows10610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10610 = true := by
  rw [show D2M8K2.u10610 = KTree.node D2M8K2.t10618 (nat_lit 23048261) (nat_lit 1168543822) (nat_lit 0) D2M8K2.t10619 from rfl, allE_node, rows10618, irow10610, rows10619]
  all_goals rfl

theorem atot10610 : totK PD2M8K2 D2M8K2.u10610 = [0, 0, 359850658170, 946351128733, 483829616185, 33002244555, 0, 0] := by
  rw [show D2M8K2.u10610 = KTree.node D2M8K2.t10618 (nat_lit 23048261) (nat_lit 1168543822) (nat_lit 0) D2M8K2.t10619 from rfl, totK_node, tot10618, tot10619]
  decide +kernel

theorem arows10612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10612 = true := by
  rw [show D2M8K2.u10612 = KTree.node D2M8K2.t10620 (nat_lit 23049732) (nat_lit 2882544673) (nat_lit 0) D2M8K2.t10621 from rfl, allE_node, rows10620, irow10612, rows10621]
  all_goals rfl

theorem atot10612 : totK PD2M8K2 D2M8K2.u10612 = [0, 0, 171545254961, 753801794385, 739193150411, 120014099694, 1171084559, 0] := by
  rw [show D2M8K2.u10612 = KTree.node D2M8K2.t10620 (nat_lit 23049732) (nat_lit 2882544673) (nat_lit 0) D2M8K2.t10621 from rfl, totK_node, tot10620, tot10621]
  decide +kernel

theorem arows10613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10613 = true := by
  rw [show D2M8K2.u10613 = KTree.node D2M8K2.t10622 (nat_lit 23051595) (nat_lit 2884008726) (nat_lit 0) D2M8K2.t10623 from rfl, allE_node, rows10622, irow10613, rows10623]
  all_goals rfl

theorem atot10613 : totK PD2M8K2 D2M8K2.u10613 = [0, 0, 241865305652, 701284840935, 613562562851, 186106999333, 11934365838, 0] := by
  rw [show D2M8K2.u10613 = KTree.node D2M8K2.t10622 (nat_lit 23051595) (nat_lit 2884008726) (nat_lit 0) D2M8K2.t10623 from rfl, totK_node, tot10622, tot10623]
  decide +kernel

theorem arows10620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10620 = true := by
  rw [show D2M8K2.u10620 = KTree.node D2M8K2.t10624 (nat_lit 23052846) (nat_lit 3833293425) (nat_lit 0) D2M8K2.t10625 from rfl, allE_node, rows10624, irow10620, rows10625]
  all_goals rfl

theorem atot10620 : totK PD2M8K2 D2M8K2.u10620 = [0, 0, 179935757967, 802376918577, 685557751026, 80875157386, 1053411165, 0] := by
  rw [show D2M8K2.u10620 = KTree.node D2M8K2.t10624 (nat_lit 23052846) (nat_lit 3833293425) (nat_lit 0) D2M8K2.t10625 from rfl, totK_node, tot10624, tot10625]
  decide +kernel

theorem arows10621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10621 = true := by
  rw [show D2M8K2.u10621 = KTree.node D2M8K2.t10626 (nat_lit 23055225) (nat_lit 1765179492) (nat_lit 0) D2M8K2.t10627 from rfl, allE_node, rows10626, irow10621, rows10627]
  all_goals rfl

theorem atot10621 : totK PD2M8K2 D2M8K2.u10621 = [0, 0, 255275087570, 775014810009, 634037244249, 116282937718, 3667207281, 0] := by
  rw [show D2M8K2.u10621 = KTree.node D2M8K2.t10626 (nat_lit 23055225) (nat_lit 1765179492) (nat_lit 0) D2M8K2.t10627 from rfl, totK_node, tot10626, tot10627]
  decide +kernel

theorem arows10623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10623 = true := by
  rw [show D2M8K2.u10623 = KTree.node D2M8K2.t10628 (nat_lit 23059017) (nat_lit 1820735469) (nat_lit 0) D2M8K2.t10629 from rfl, allE_node, rows10628, irow10623, rows10629]
  all_goals rfl

theorem atot10623 : totK PD2M8K2 D2M8K2.u10623 = [0, 281514924461, 780861721623, 561343578491, 165102399637, 11712179621, 0, 0] := by
  rw [show D2M8K2.u10623 = KTree.node D2M8K2.t10628 (nat_lit 23059017) (nat_lit 1820735469) (nat_lit 0) D2M8K2.t10629 from rfl, totK_node, tot10628, tot10629]
  decide +kernel

theorem arows10624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10624 = true := by
  rw [show D2M8K2.u10624 = KTree.node D2M8K2.t10630 (nat_lit 23060265) (nat_lit 1892005393) (nat_lit 0) D2M8K2.t10631 from rfl, allE_node, rows10630, irow10624, rows10631]
  all_goals rfl

theorem atot10624 : totK PD2M8K2 D2M8K2.u10624 = [0, 127232457136, 700722632032, 802233676381, 134869446901, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10624 = KTree.node D2M8K2.t10630 (nat_lit 23060265) (nat_lit 1892005393) (nat_lit 0) D2M8K2.t10631 from rfl, totK_node, tot10630, tot10631]
  decide +kernel

theorem arows10627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10627 = true := by
  rw [show D2M8K2.u10627 = KTree.node D2M8K2.t10632 (nat_lit 23062588) (nat_lit 3920265894) (nat_lit 0) D2M8K2.t10633 from rfl, allE_node, rows10632, irow10627, rows10633]
  all_goals rfl

theorem atot10627 : totK PD2M8K2 D2M8K2.u10627 = [0, 354537707310, 877958784264, 535484957043, 53099591286, 0, 0, 0] := by
  rw [show D2M8K2.u10627 = KTree.node D2M8K2.t10632 (nat_lit 23062588) (nat_lit 3920265894) (nat_lit 0) D2M8K2.t10633 from rfl, totK_node, tot10632, tot10633]
  decide +kernel

theorem arows10628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10628 = true := by
  rw [show D2M8K2.u10628 = KTree.node D2M8K2.t10634 (nat_lit 23064121) (nat_lit 804043985) (nat_lit 0) D2M8K2.t10635 from rfl, allE_node, rows10634, irow10628, rows10635]
  all_goals rfl

theorem atot10628 : totK PD2M8K2 D2M8K2.u10628 = [0, 68188677921, 534984484718, 828932279789, 344479145737, 28002240837, 0, 0] := by
  rw [show D2M8K2.u10628 = KTree.node D2M8K2.t10634 (nat_lit 23064121) (nat_lit 804043985) (nat_lit 0) D2M8K2.t10635 from rfl, totK_node, tot10634, tot10635]
  decide +kernel

theorem arows10630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10630 = true := by
  rw [show D2M8K2.u10630 = KTree.node D2M8K2.t10636 (nat_lit 23065416) (nat_lit 3583302807) (nat_lit 0) D2M8K2.t10637 from rfl, allE_node, rows10636, irow10630, rows10637]
  all_goals rfl

theorem atot10630 : totK PD2M8K2 D2M8K2.u10630 = [0, 222199482561, 658410357516, 677091514840, 237125098605, 7957747042, 0, 0] := by
  rw [show D2M8K2.u10630 = KTree.node D2M8K2.t10636 (nat_lit 23065416) (nat_lit 3583302807) (nat_lit 0) D2M8K2.t10637 from rfl, totK_node, tot10636, tot10637]
  decide +kernel

theorem arows10631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10631 = true := by
  rw [show D2M8K2.u10631 = KTree.node D2M8K2.t10638 (nat_lit 23066934) (nat_lit 2650149329) (nat_lit 0) D2M8K2.t10639 from rfl, allE_node, rows10638, irow10631, rows10639]
  all_goals rfl

theorem atot10631 : totK PD2M8K2 D2M8K2.u10631 = [0, 178747526861, 763390862130, 719943441566, 110896812191, 1164319620, 0, 0] := by
  rw [show D2M8K2.u10631 = KTree.node D2M8K2.t10638 (nat_lit 23066934) (nat_lit 2650149329) (nat_lit 0) D2M8K2.t10639 from rfl, totK_node, tot10638, tot10639]
  decide +kernel

theorem arows10635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10635 = true := by
  rw [show D2M8K2.u10635 = KTree.node D2M8K2.t10640 (nat_lit 23068885) (nat_lit 1267650260) (nat_lit 0) D2M8K2.t10641 from rfl, allE_node, rows10640, irow10635, rows10641]
  all_goals rfl

theorem atot10635 : totK PD2M8K2 D2M8K2.u10635 = [0, 228912322449, 679704325206, 671613041700, 193595994383, 11885407614, 0, 0] := by
  rw [show D2M8K2.u10635 = KTree.node D2M8K2.t10640 (nat_lit 23068885) (nat_lit 1267650260) (nat_lit 0) D2M8K2.t10641 from rfl, totK_node, tot10640, tot10641]
  decide +kernel

theorem arows10636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10636 = true := by
  rw [show D2M8K2.u10636 = KTree.node D2M8K2.t10642 (nat_lit 23070374) (nat_lit 3864524786) (nat_lit 0) D2M8K2.t10643 from rfl, allE_node, rows10642, irow10636, rows10643]
  all_goals rfl

theorem atot10636 : totK PD2M8K2 D2M8K2.u10636 = [0, 193008397199, 764112171615, 717557131085, 122067463605, 1198073392, 0, 0] := by
  rw [show D2M8K2.u10636 = KTree.node D2M8K2.t10642 (nat_lit 23070374) (nat_lit 3864524786) (nat_lit 0) D2M8K2.t10643 from rfl, totK_node, tot10642, tot10643]
  decide +kernel

theorem arows10638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10638 = true := by
  rw [show D2M8K2.u10638 = KTree.node D2M8K2.t10644 (nat_lit 23072098) (nat_lit 4059225748) (nat_lit 0) D2M8K2.t10645 from rfl, allE_node, rows10644, irow10638, rows10645]
  all_goals rfl

theorem atot10638 : totK PD2M8K2 D2M8K2.u10638 = [0, 175967501358, 654334382585, 742307492654, 223089715153, 12052611869, 0, 0] := by
  rw [show D2M8K2.u10638 = KTree.node D2M8K2.t10644 (nat_lit 23072098) (nat_lit 4059225748) (nat_lit 0) D2M8K2.t10645 from rfl, totK_node, tot10644, tot10645]
  decide +kernel

theorem arows10639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10639 = true := by
  rw [show D2M8K2.u10639 = KTree.node D2M8K2.t10646 (nat_lit 23073421) (nat_lit 1383681404) (nat_lit 0) D2M8K2.t10647 from rfl, allE_node, rows10646, irow10639, rows10647]
  all_goals rfl

theorem atot10639 : totK PD2M8K2 D2M8K2.u10639 = [0, 264671176949, 824672214934, 626253892166, 93317770950, 1096505104, 0, 0] := by
  rw [show D2M8K2.u10639 = KTree.node D2M8K2.t10646 (nat_lit 23073421) (nat_lit 1383681404) (nat_lit 0) D2M8K2.t10647 from rfl, totK_node, tot10646, tot10647]
  decide +kernel

theorem arows10642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10642 = true := by
  rw [show D2M8K2.u10642 = KTree.node D2M8K2.t10648 (nat_lit 23075352) (nat_lit 3226176481) (nat_lit 0) D2M8K2.t10649 from rfl, allE_node, rows10648, irow10642, rows10649]
  all_goals rfl

theorem atot10642 : totK PD2M8K2 D2M8K2.u10642 = [0, 0, 470960100757, 986417103401, 312523504265, 13624150839, 0, 0] := by
  rw [show D2M8K2.u10642 = KTree.node D2M8K2.t10648 (nat_lit 23075352) (nat_lit 3226176481) (nat_lit 0) D2M8K2.t10649 from rfl, totK_node, tot10648, tot10649]
  decide +kernel

theorem arows10643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10643 = true := by
  rw [show D2M8K2.u10643 = KTree.node D2M8K2.t10650 (nat_lit 23080659) (nat_lit 2170187974) (nat_lit 0) D2M8K2.t10651 from rfl, allE_node, rows10650, irow10643, rows10651]
  all_goals rfl

theorem atot10643 : totK PD2M8K2 D2M8K2.u10643 = [0, 0, 237583927598, 811228074565, 590618153926, 77442876661, 1138244013, 0] := by
  rw [show D2M8K2.u10643 = KTree.node D2M8K2.t10650 (nat_lit 23080659) (nat_lit 2170187974) (nat_lit 0) D2M8K2.t10651 from rfl, totK_node, tot10650, tot10651]
  decide +kernel

theorem arows10645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10645 = true := by
  rw [show D2M8K2.u10645 = KTree.node D2M8K2.t10652 (nat_lit 23083173) (nat_lit 1404666214) (nat_lit 0) D2M8K2.t10653 from rfl, allE_node, rows10652, irow10645, rows10653]
  all_goals rfl

theorem atot10645 : totK PD2M8K2 D2M8K2.u10645 = [0, 0, 268450015286, 861293908063, 594074257778, 60235749610, 0, 0] := by
  rw [show D2M8K2.u10645 = KTree.node D2M8K2.t10652 (nat_lit 23083173) (nat_lit 1404666214) (nat_lit 0) D2M8K2.t10653 from rfl, totK_node, tot10652, tot10653]
  decide +kernel

theorem arows10646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10646 = true := by
  rw [show D2M8K2.u10646 = KTree.node D2M8K2.t10654 (nat_lit 23086202) (nat_lit 1817040374) (nat_lit 0) D2M8K2.t10655 from rfl, allE_node, rows10654, irow10646, rows10655]
  all_goals rfl

theorem atot10646 : totK PD2M8K2 D2M8K2.u10646 = [0, 0, 409554330875, 984183017504, 392849629473, 15111599410, 0, 0] := by
  rw [show D2M8K2.u10646 = KTree.node D2M8K2.t10654 (nat_lit 23086202) (nat_lit 1817040374) (nat_lit 0) D2M8K2.t10655 from rfl, totK_node, tot10654, tot10655]
  decide +kernel

theorem arows10651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10651 = true := by
  rw [show D2M8K2.u10651 = KTree.node D2M8K2.t10656 (nat_lit 23089593) (nat_lit 1781299875) (nat_lit 0) D2M8K2.t10657 from rfl, allE_node, rows10656, irow10651, rows10657]
  all_goals rfl

theorem atot10651 : totK PD2M8K2 D2M8K2.u10651 = [0, 0, 367355756345, 943751607678, 449510615968, 24560242094, 0, 0] := by
  rw [show D2M8K2.u10651 = KTree.node D2M8K2.t10656 (nat_lit 23089593) (nat_lit 1781299875) (nat_lit 0) D2M8K2.t10657 from rfl, totK_node, tot10656, tot10657]
  decide +kernel

theorem arows10652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10652 = true := by
  rw [show D2M8K2.u10652 = KTree.node D2M8K2.t10658 (nat_lit 23091106) (nat_lit 4059225748) (nat_lit 0) D2M8K2.t10659 from rfl, allE_node, rows10658, irow10652, rows10659]
  all_goals rfl

theorem atot10652 : totK PD2M8K2 D2M8K2.u10652 = [0, 0, 366945711374, 954166367549, 449004284452, 27845021940, 0, 0] := by
  rw [show D2M8K2.u10652 = KTree.node D2M8K2.t10658 (nat_lit 23091106) (nat_lit 4059225748) (nat_lit 0) D2M8K2.t10659 from rfl, totK_node, tot10658, tot10659]
  decide +kernel

theorem arows10654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10654 = true := by
  rw [show D2M8K2.u10654 = KTree.node D2M8K2.t10660 (nat_lit 23094090) (nat_lit 3580844901) (nat_lit 0) D2M8K2.t10661 from rfl, allE_node, rows10660, irow10654, rows10661]
  all_goals rfl

theorem atot10654 : totK PD2M8K2 D2M8K2.u10654 = [0, 0, 267065533544, 829739041546, 585972404085, 79350971238, 1095107716, 0] := by
  rw [show D2M8K2.u10654 = KTree.node D2M8K2.t10660 (nat_lit 23094090) (nat_lit 3580844901) (nat_lit 0) D2M8K2.t10661 from rfl, totK_node, tot10660, tot10661]
  decide +kernel

theorem arows10655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10655 = true := by
  rw [show D2M8K2.u10655 = KTree.node D2M8K2.t10662 (nat_lit 23096034) (nat_lit 2247422428) (nat_lit 0) D2M8K2.t10663 from rfl, allE_node, rows10662, irow10655, rows10663]
  all_goals rfl

theorem atot10655 : totK PD2M8K2 D2M8K2.u10655 = [0, 0, 175735631326, 739033993851, 701241420184, 141192955345, 3882006667, 0] := by
  rw [show D2M8K2.u10655 = KTree.node D2M8K2.t10662 (nat_lit 23096034) (nat_lit 2247422428) (nat_lit 0) D2M8K2.t10663 from rfl, totK_node, tot10662, tot10663]
  decide +kernel

theorem arows10658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10658 = true := by
  rw [show D2M8K2.u10658 = KTree.node D2M8K2.t10664 (nat_lit 23142784) (nat_lit 2892258570) (nat_lit 0) D2M8K2.t10665 from rfl, allE_node, rows10664, irow10658, rows10665]
  all_goals rfl

theorem atot10658 : totK PD2M8K2 D2M8K2.u10658 = [0, 0, 256016219470, 795404969965, 620337178381, 98943260416, 1369150432, 0] := by
  rw [show D2M8K2.u10658 = KTree.node D2M8K2.t10664 (nat_lit 23142784) (nat_lit 2892258570) (nat_lit 0) D2M8K2.t10665 from rfl, totK_node, tot10664, tot10665]
  decide +kernel

theorem arows10659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10659 = true := by
  rw [show D2M8K2.u10659 = KTree.node D2M8K2.t10666 (nat_lit 23148344) (nat_lit 3688266149) (nat_lit 0) D2M8K2.t10667 from rfl, allE_node, rows10666, irow10659, rows10667]
  all_goals rfl

theorem atot10659 : totK PD2M8K2 D2M8K2.u10659 = [0, 0, 227602364414, 825635080227, 680833271302, 56819593052, 0, 0] := by
  rw [show D2M8K2.u10659 = KTree.node D2M8K2.t10666 (nat_lit 23148344) (nat_lit 3688266149) (nat_lit 0) D2M8K2.t10667 from rfl, totK_node, tot10666, tot10667]
  decide +kernel

theorem arows10661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10661 = true := by
  rw [show D2M8K2.u10661 = KTree.node D2M8K2.t10668 (nat_lit 23150088) (nat_lit 3605777839) (nat_lit 0) D2M8K2.t10669 from rfl, allE_node, rows10668, irow10661, rows10669]
  all_goals rfl

theorem atot10661 : totK PD2M8K2 D2M8K2.u10661 = [0, 0, 149401326491, 758901283831, 758498658412, 87545363239, 1164319620, 0] := by
  rw [show D2M8K2.u10661 = KTree.node D2M8K2.t10668 (nat_lit 23150088) (nat_lit 3605777839) (nat_lit 0) D2M8K2.t10669 from rfl, totK_node, tot10668, tot10669]
  decide +kernel

theorem arows10662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10662 = true := by
  rw [show D2M8K2.u10662 = KTree.node D2M8K2.t10670 (nat_lit 23152643) (nat_lit 2643417883) (nat_lit 0) D2M8K2.t10671 from rfl, allE_node, rows10670, irow10662, rows10671]
  all_goals rfl

theorem atot10662 : totK PD2M8K2 D2M8K2.u10662 = [0, 0, 374177624693, 933494949562, 468856928431, 27211493619, 0, 0] := by
  rw [show D2M8K2.u10662 = KTree.node D2M8K2.t10670 (nat_lit 23152643) (nat_lit 2643417883) (nat_lit 0) D2M8K2.t10671 from rfl, totK_node, tot10670, tot10671]
  decide +kernel

theorem arows10666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10666 = true := by
  rw [show D2M8K2.u10666 = KTree.node D2M8K2.t10672 (nat_lit 23154364) (nat_lit 2044173677) (nat_lit 0) D2M8K2.t10673 from rfl, allE_node, rows10672, irow10666, rows10673]
  all_goals rfl

theorem atot10666 : totK PD2M8K2 D2M8K2.u10666 = [0, 0, 37322106084, 524243844406, 913488763959, 265884725519, 13184317400, 0] := by
  rw [show D2M8K2.u10666 = KTree.node D2M8K2.t10672 (nat_lit 23154364) (nat_lit 2044173677) (nat_lit 0) D2M8K2.t10673 from rfl, totK_node, tot10672, tot10673]
  decide +kernel

theorem arows10667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10667 = true := by
  rw [show D2M8K2.u10667 = KTree.node D2M8K2.t10674 (nat_lit 23155798) (nat_lit 3199409110) (nat_lit 0) D2M8K2.t10675 from rfl, allE_node, rows10674, irow10667, rows10675]
  all_goals rfl

theorem atot10667 : totK PD2M8K2 D2M8K2.u10667 = [0, 0, 360721447533, 893647622417, 476195915139, 37853814743, 0, 0] := by
  rw [show D2M8K2.u10667 = KTree.node D2M8K2.t10674 (nat_lit 23155798) (nat_lit 3199409110) (nat_lit 0) D2M8K2.t10675 from rfl, totK_node, tot10674, tot10675]
  decide +kernel

theorem arows10669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10669 = true := by
  rw [show D2M8K2.u10669 = KTree.node D2M8K2.t10676 (nat_lit 23157505) (nat_lit 1545447192) (nat_lit 0) D2M8K2.t10677 from rfl, allE_node, rows10676, irow10669, rows10677]
  all_goals rfl

theorem atot10669 : totK PD2M8K2 D2M8K2.u10669 = [0, 0, 74394908520, 618956679089, 887951014787, 185304240726, 4980514959, 0] := by
  rw [show D2M8K2.u10669 = KTree.node D2M8K2.t10676 (nat_lit 23157505) (nat_lit 1545447192) (nat_lit 0) D2M8K2.t10677 from rfl, totK_node, tot10676, tot10677]
  decide +kernel

theorem arows10670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10670 = true := by
  rw [show D2M8K2.u10670 = KTree.node D2M8K2.t10678 (nat_lit 23159670) (nat_lit 3812646336) (nat_lit 0) D2M8K2.t10679 from rfl, allE_node, rows10678, irow10670, rows10679]
  all_goals rfl

theorem atot10670 : totK PD2M8K2 D2M8K2.u10670 = [0, 0, 306348245093, 891839852483, 532573480068, 56933818584, 1268739303, 0] := by
  rw [show D2M8K2.u10670 = KTree.node D2M8K2.t10678 (nat_lit 23159670) (nat_lit 3812646336) (nat_lit 0) D2M8K2.t10679 from rfl, totK_node, tot10678, tot10679]
  decide +kernel

theorem arows10673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10673 = true := by
  rw [show D2M8K2.u10673 = KTree.node D2M8K2.t10680 (nat_lit 23162276) (nat_lit 2777369328) (nat_lit 0) D2M8K2.t10681 from rfl, allE_node, rows10680, irow10673, rows10681]
  all_goals rfl

theorem atot10673 : totK PD2M8K2 D2M8K2.u10673 = [0, 0, 0, 491151135881, 977598197823, 275681258420, 10856061908, 0] := by
  rw [show D2M8K2.u10673 = KTree.node D2M8K2.t10680 (nat_lit 23162276) (nat_lit 2777369328) (nat_lit 0) D2M8K2.t10681 from rfl, totK_node, tot10680, tot10681]
  decide +kernel

theorem arows10674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10674 = true := by
  rw [show D2M8K2.u10674 = KTree.node D2M8K2.t10682 (nat_lit 23163939) (nat_lit 1929879276) (nat_lit 0) D2M8K2.t10683 from rfl, allE_node, rows10682, irow10674, rows10683]
  all_goals rfl

theorem atot10674 : totK PD2M8K2 D2M8K2.u10674 = [0, 0, 0, 164072893226, 799083245434, 636323131789, 77240724220, 1209030869] := by
  rw [show D2M8K2.u10674 = KTree.node D2M8K2.t10682 (nat_lit 23163939) (nat_lit 1929879276) (nat_lit 0) D2M8K2.t10683 from rfl, totK_node, tot10682, tot10683]
  decide +kernel

theorem arows10676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10676 = true := by
  rw [show D2M8K2.u10676 = KTree.node D2M8K2.t10684 (nat_lit 23170186) (nat_lit 2903794325) (nat_lit 0) D2M8K2.t10685 from rfl, allE_node, rows10684, irow10676, rows10685]
  all_goals rfl

theorem atot10676 : totK PD2M8K2 D2M8K2.u10676 = [0, 0, 0, 464947501264, 1003092941178, 272568086208, 4966990951, 0] := by
  rw [show D2M8K2.u10676 = KTree.node D2M8K2.t10684 (nat_lit 23170186) (nat_lit 2903794325) (nat_lit 0) D2M8K2.t10685 from rfl, totK_node, tot10684, tot10685]
  decide +kernel

theorem arows10677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10677 = true := by
  rw [show D2M8K2.u10677 = KTree.node D2M8K2.t10686 (nat_lit 23173796) (nat_lit 3067217043) (nat_lit 0) D2M8K2.t10687 from rfl, allE_node, rows10686, irow10677, rows10687]
  all_goals rfl

theorem atot10677 : totK PD2M8K2 D2M8K2.u10677 = [0, 0, 0, 469126000491, 958707723820, 313628772357, 13622839862, 0] := by
  rw [show D2M8K2.u10677 = KTree.node D2M8K2.t10686 (nat_lit 23173796) (nat_lit 3067217043) (nat_lit 0) D2M8K2.t10687 from rfl, totK_node, tot10686, tot10687]
  decide +kernel

theorem arows10683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10683 = true := by
  rw [show D2M8K2.u10683 = KTree.node D2M8K2.t10688 (nat_lit 23177066) (nat_lit 2493031282) (nat_lit 0) D2M8K2.t10689 from rfl, allE_node, rows10688, irow10683, rows10689]
  all_goals rfl

theorem atot10683 : totK PD2M8K2 D2M8K2.u10683 = [0, 0, 0, 376592723460, 974841576618, 362836768021, 16184734748, 0] := by
  rw [show D2M8K2.u10683 = KTree.node D2M8K2.t10688 (nat_lit 23177066) (nat_lit 2493031282) (nat_lit 0) D2M8K2.t10689 from rfl, totK_node, tot10688, tot10689]
  decide +kernel

theorem arows10684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10684 = true := by
  rw [show D2M8K2.u10684 = KTree.node D2M8K2.t10690 (nat_lit 23186827) (nat_lit 1742990493) (nat_lit 0) D2M8K2.t10691 from rfl, allE_node, rows10690, irow10684, rows10691]
  all_goals rfl

theorem atot10684 : totK PD2M8K2 D2M8K2.u10684 = [0, 0, 268165479436, 867942532240, 651708170917, 65390788920, 0, 0] := by
  rw [show D2M8K2.u10684 = KTree.node D2M8K2.t10690 (nat_lit 23186827) (nat_lit 1742990493) (nat_lit 0) D2M8K2.t10691 from rfl, totK_node, tot10690, tot10691]
  decide +kernel

theorem arows10686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10686 = true := by
  rw [show D2M8K2.u10686 = KTree.node D2M8K2.t10692 (nat_lit 23188354) (nat_lit 4046144306) (nat_lit 0) D2M8K2.t10693 from rfl, allE_node, rows10692, irow10686, rows10693]
  all_goals rfl

theorem atot10686 : totK PD2M8K2 D2M8K2.u10686 = [0, 0, 172214411719, 721106025128, 758350834527, 189867721960, 9977052014, 0] := by
  rw [show D2M8K2.u10686 = KTree.node D2M8K2.t10692 (nat_lit 23188354) (nat_lit 4046144306) (nat_lit 0) D2M8K2.t10693 from rfl, totK_node, tot10692, tot10693]
  decide +kernel

theorem arows10687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10687 = true := by
  rw [show D2M8K2.u10687 = KTree.node D2M8K2.t10694 (nat_lit 23190110) (nat_lit 3939444844) (nat_lit 0) D2M8K2.t10695 from rfl, allE_node, rows10694, irow10687, rows10695]
  all_goals rfl

theorem atot10687 : totK PD2M8K2 D2M8K2.u10687 = [0, 0, 264192326977, 742347351729, 636419916508, 174805111803, 5430665091, 0] := by
  rw [show D2M8K2.u10687 = KTree.node D2M8K2.t10694 (nat_lit 23190110) (nat_lit 3939444844) (nat_lit 0) D2M8K2.t10695 from rfl, totK_node, tot10694, tot10695]
  decide +kernel

theorem arows10690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10690 = true := by
  rw [show D2M8K2.u10690 = KTree.node D2M8K2.t10696 (nat_lit 23193590) (nat_lit 3999417673) (nat_lit 0) D2M8K2.t10697 from rfl, allE_node, rows10696, irow10690, rows10697]
  all_goals rfl

theorem atot10690 : totK PD2M8K2 D2M8K2.u10690 = [0, 0, 402222640287, 964561826131, 448280521295, 32729142033, 0, 0] := by
  rw [show D2M8K2.u10690 = KTree.node D2M8K2.t10696 (nat_lit 23193590) (nat_lit 3999417673) (nat_lit 0) D2M8K2.t10697 from rfl, totK_node, tot10696, tot10697]
  decide +kernel

theorem arows10691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10691 = true := by
  rw [show D2M8K2.u10691 = KTree.node D2M8K2.t10698 (nat_lit 23195260) (nat_lit 3734392008) (nat_lit 0) D2M8K2.t10699 from rfl, allE_node, rows10698, irow10691, rows10699]
  all_goals rfl

theorem atot10691 : totK PD2M8K2 D2M8K2.u10691 = [0, 0, 131816429019, 704228765319, 805087446210, 162186737589, 7316020427, 0] := by
  rw [show D2M8K2.u10691 = KTree.node D2M8K2.t10698 (nat_lit 23195260) (nat_lit 3734392008) (nat_lit 0) D2M8K2.t10699 from rfl, totK_node, tot10698, tot10699]
  decide +kernel

theorem arows10693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10693 = true := by
  rw [show D2M8K2.u10693 = KTree.node D2M8K2.t10700 (nat_lit 23197136) (nat_lit 3729112393) (nat_lit 0) D2M8K2.t10701 from rfl, allE_node, rows10700, irow10693, rows10701]
  all_goals rfl

theorem atot10693 : totK PD2M8K2 D2M8K2.u10693 = [0, 0, 328595392036, 848138446658, 538647524693, 85371273474, 2566665356, 0] := by
  rw [show D2M8K2.u10693 = KTree.node D2M8K2.t10700 (nat_lit 23197136) (nat_lit 3729112393) (nat_lit 0) D2M8K2.t10701 from rfl, totK_node, tot10700, tot10701]
  decide +kernel

theorem arows10694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10694 = true := by
  rw [show D2M8K2.u10694 = KTree.node D2M8K2.t10702 (nat_lit 23198768) (nat_lit 3746383347) (nat_lit 0) D2M8K2.t10703 from rfl, allE_node, rows10702, irow10694, rows10703]
  all_goals rfl

theorem atot10694 : totK PD2M8K2 D2M8K2.u10694 = [0, 0, 91681601894, 717302819840, 871880641310, 126999916354, 0, 0] := by
  rw [show D2M8K2.u10694 = KTree.node D2M8K2.t10702 (nat_lit 23198768) (nat_lit 3746383347) (nat_lit 0) D2M8K2.t10703 from rfl, totK_node, tot10702, tot10703]
  decide +kernel

theorem arows10698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10698 = true := by
  rw [show D2M8K2.u10698 = KTree.node D2M8K2.t10704 (nat_lit 23201128) (nat_lit 3185218745) (nat_lit 0) D2M8K2.t10705 from rfl, allE_node, rows10704, irow10698, rows10705]
  all_goals rfl

theorem atot10698 : totK PD2M8K2 D2M8K2.u10698 = [0, 0, 420827545220, 934288507822, 456648859032, 60741833598, 2813333534, 0] := by
  rw [show D2M8K2.u10698 = KTree.node D2M8K2.t10704 (nat_lit 23201128) (nat_lit 3185218745) (nat_lit 0) D2M8K2.t10705 from rfl, totK_node, tot10704, tot10705]
  decide +kernel

theorem arows10699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10699 = true := by
  rw [show D2M8K2.u10699 = KTree.node D2M8K2.t10706 (nat_lit 23225505) (nat_lit 1847415472) (nat_lit 0) D2M8K2.t10707 from rfl, allE_node, rows10706, irow10699, rows10707]
  all_goals rfl

theorem atot10699 : totK PD2M8K2 D2M8K2.u10699 = [0, 0, 305204888837, 915326444808, 503884299670, 31367843141, 0, 0] := by
  rw [show D2M8K2.u10699 = KTree.node D2M8K2.t10706 (nat_lit 23225505) (nat_lit 1847415472) (nat_lit 0) D2M8K2.t10707 from rfl, totK_node, tot10706, tot10707]
  decide +kernel

theorem arows10701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10701 = true := by
  rw [show D2M8K2.u10701 = KTree.node D2M8K2.t10708 (nat_lit 23228096) (nat_lit 3795598104) (nat_lit 0) D2M8K2.t10709 from rfl, allE_node, rows10708, irow10701, rows10709]
  all_goals rfl

theorem atot10701 : totK PD2M8K2 D2M8K2.u10701 = [0, 0, 183522139230, 761618097841, 770770938906, 93065446916, 1310166938, 0] := by
  rw [show D2M8K2.u10701 = KTree.node D2M8K2.t10708 (nat_lit 23228096) (nat_lit 3795598104) (nat_lit 0) D2M8K2.t10709 from rfl, totK_node, tot10708, tot10709]
  decide +kernel

theorem arows10702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10702 = true := by
  rw [show D2M8K2.u10702 = KTree.node D2M8K2.t10710 (nat_lit 23231356) (nat_lit 3854718101) (nat_lit 0) D2M8K2.t10711 from rfl, allE_node, rows10710, irow10702, rows10711]
  all_goals rfl

theorem atot10702 : totK PD2M8K2 D2M8K2.u10702 = [0, 0, 484629994996, 987027864424, 356238660479, 16692344984, 0, 0] := by
  rw [show D2M8K2.u10702 = KTree.node D2M8K2.t10710 (nat_lit 23231356) (nat_lit 3854718101) (nat_lit 0) D2M8K2.t10711 from rfl, totK_node, tot10710, tot10711]
  decide +kernel

theorem arows10705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10705 = true := by
  rw [show D2M8K2.u10705 = KTree.node D2M8K2.t10712 (nat_lit 23232877) (nat_lit 1054169322) (nat_lit 0) D2M8K2.t10713 from rfl, allE_node, rows10712, irow10705, rows10713]
  all_goals rfl

theorem atot10705 : totK PD2M8K2 D2M8K2.u10705 = [0, 0, 159767150191, 774098783199, 752734099505, 96002752401, 1164319620, 0] := by
  rw [show D2M8K2.u10705 = KTree.node D2M8K2.t10712 (nat_lit 23232877) (nat_lit 1054169322) (nat_lit 0) D2M8K2.t10713 from rfl, totK_node, tot10712, tot10713]
  decide +kernel

theorem arows10706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10706 = true := by
  rw [show D2M8K2.u10706 = KTree.node D2M8K2.t10714 (nat_lit 23238475) (nat_lit 1785877122) (nat_lit 0) D2M8K2.t10715 from rfl, allE_node, rows10714, irow10706, rows10715]
  all_goals rfl

theorem atot10706 : totK PD2M8K2 D2M8K2.u10706 = [0, 0, 291074439876, 815246784341, 570017207700, 97679180835, 3462014130, 0] := by
  rw [show D2M8K2.u10706 = KTree.node D2M8K2.t10714 (nat_lit 23238475) (nat_lit 1785877122) (nat_lit 0) D2M8K2.t10715 from rfl, totK_node, tot10714, tot10715]
  decide +kernel

theorem arows10708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10708 = true := by
  rw [show D2M8K2.u10708 = KTree.node D2M8K2.t10716 (nat_lit 23239989) (nat_lit 1738746426) (nat_lit 0) D2M8K2.t10717 from rfl, allE_node, rows10716, irow10708, rows10717]
  all_goals rfl

theorem atot10708 : totK PD2M8K2 D2M8K2.u10708 = [0, 0, 128154751257, 756241660869, 783580898111, 104613158457, 1096505104, 0] := by
  rw [show D2M8K2.u10708 = KTree.node D2M8K2.t10716 (nat_lit 23239989) (nat_lit 1738746426) (nat_lit 0) D2M8K2.t10717 from rfl, totK_node, tot10716, tot10717]
  decide +kernel

theorem arows10709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10709 = true := by
  rw [show D2M8K2.u10709 = KTree.node D2M8K2.t10718 (nat_lit 23266608) (nat_lit 3384481187) (nat_lit 0) D2M8K2.t10719 from rfl, allE_node, rows10718, irow10709, rows10719]
  all_goals rfl

theorem atot10709 : totK PD2M8K2 D2M8K2.u10709 = [0, 0, 326932195755, 852437234497, 484181638677, 82828018341, 3884009855, 0] := by
  rw [show D2M8K2.u10709 = KTree.node D2M8K2.t10718 (nat_lit 23266608) (nat_lit 3384481187) (nat_lit 0) D2M8K2.t10719 from rfl, totK_node, tot10718, tot10719]
  decide +kernel

theorem arows10714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10714 = true := by
  rw [show D2M8K2.u10714 = KTree.node D2M8K2.t10720 (nat_lit 23268198) (nat_lit 2503821602) (nat_lit 0) D2M8K2.t10721 from rfl, allE_node, rows10720, irow10714, rows10721]
  all_goals rfl

theorem atot10714 : totK PD2M8K2 D2M8K2.u10714 = [0, 0, 140613018324, 692204104922, 828004748041, 122456263120, 1310517177, 0] := by
  rw [show D2M8K2.u10714 = KTree.node D2M8K2.t10720 (nat_lit 23268198) (nat_lit 2503821602) (nat_lit 0) D2M8K2.t10721 from rfl, totK_node, tot10720, tot10721]
  decide +kernel

theorem arows10715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10715 = true := by
  rw [show D2M8K2.u10715 = KTree.node D2M8K2.t10722 (nat_lit 23270330) (nat_lit 4054986831) (nat_lit 0) D2M8K2.t10723 from rfl, allE_node, rows10722, irow10715, rows10723]
  all_goals rfl

theorem atot10715 : totK PD2M8K2 D2M8K2.u10715 = [0, 0, 352922932841, 936612603181, 516133727020, 38738492951, 0, 0] := by
  rw [show D2M8K2.u10715 = KTree.node D2M8K2.t10722 (nat_lit 23270330) (nat_lit 4054986831) (nat_lit 0) D2M8K2.t10723 from rfl, totK_node, tot10722, tot10723]
  decide +kernel

theorem arows10717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10717 = true := by
  rw [show D2M8K2.u10717 = KTree.node D2M8K2.t10724 (nat_lit 23272074) (nat_lit 3704873797) (nat_lit 0) D2M8K2.t10725 from rfl, allE_node, rows10724, irow10717, rows10725]
  all_goals rfl

theorem atot10717 : totK PD2M8K2 D2M8K2.u10717 = [0, 0, 85737809554, 545233233782, 867561962891, 306657190560, 15066332673, 0] := by
  rw [show D2M8K2.u10717 = KTree.node D2M8K2.t10724 (nat_lit 23272074) (nat_lit 3704873797) (nat_lit 0) D2M8K2.t10725 from rfl, totK_node, tot10724, tot10725]
  decide +kernel

theorem arows10718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10718 = true := by
  rw [show D2M8K2.u10718 = KTree.node D2M8K2.t10726 (nat_lit 23277174) (nat_lit 3827012122) (nat_lit 0) D2M8K2.t10727 from rfl, allE_node, rows10726, irow10718, rows10727]
  all_goals rfl

theorem atot10718 : totK PD2M8K2 D2M8K2.u10718 = [0, 0, 353815190900, 941844537403, 502472033512, 34283031837, 0, 0] := by
  rw [show D2M8K2.u10718 = KTree.node D2M8K2.t10726 (nat_lit 23277174) (nat_lit 3827012122) (nat_lit 0) D2M8K2.t10727 from rfl, totK_node, tot10726, tot10727]
  decide +kernel

theorem arows10721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10721 = true := by
  rw [show D2M8K2.u10721 = KTree.node D2M8K2.t10728 (nat_lit 23278851) (nat_lit 3615454077) (nat_lit 0) D2M8K2.t10729 from rfl, allE_node, rows10728, irow10721, rows10729]
  all_goals rfl

theorem atot10721 : totK PD2M8K2 D2M8K2.u10721 = [0, 0, 0, 483358483362, 987989595261, 298994401680, 13170675918, 0] := by
  rw [show D2M8K2.u10721 = KTree.node D2M8K2.t10728 (nat_lit 23278851) (nat_lit 3615454077) (nat_lit 0) D2M8K2.t10729 from rfl, totK_node, tot10728, tot10729]
  decide +kernel

theorem arows10722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10722 = true := by
  rw [show D2M8K2.u10722 = KTree.node D2M8K2.t10730 (nat_lit 23280204) (nat_lit 3409983838) (nat_lit 0) D2M8K2.t10731 from rfl, allE_node, rows10730, irow10722, rows10731]
  all_goals rfl

theorem atot10722 : totK PD2M8K2 D2M8K2.u10722 = [0, 0, 381589446547, 905311917410, 461090080112, 34669886094, 0, 0] := by
  rw [show D2M8K2.u10722 = KTree.node D2M8K2.t10730 (nat_lit 23280204) (nat_lit 3409983838) (nat_lit 0) D2M8K2.t10731 from rfl, totK_node, tot10730, tot10731]
  decide +kernel

theorem arows10724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10724 = true := by
  rw [show D2M8K2.u10724 = KTree.node D2M8K2.t10732 (nat_lit 23281930) (nat_lit 2394657956) (nat_lit 0) D2M8K2.t10733 from rfl, allE_node, rows10732, irow10724, rows10733]
  all_goals rfl

theorem atot10724 : totK PD2M8K2 D2M8K2.u10724 = [0, 0, 72383964705, 619150086968, 889722807951, 188810611724, 4980514959, 0] := by
  rw [show D2M8K2.u10724 = KTree.node D2M8K2.t10732 (nat_lit 23281930) (nat_lit 2394657956) (nat_lit 0) D2M8K2.t10733 from rfl, totK_node, tot10732, tot10733]
  decide +kernel

theorem arows10725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10725 = true := by
  rw [show D2M8K2.u10725 = KTree.node D2M8K2.t10734 (nat_lit 23284044) (nat_lit 2944299798) (nat_lit 0) D2M8K2.t10735 from rfl, allE_node, rows10734, irow10725, rows10735]
  all_goals rfl

theorem atot10725 : totK PD2M8K2 D2M8K2.u10725 = [0, 0, 305344613526, 904830989876, 570822135574, 46184901499, 0, 0] := by
  rw [show D2M8K2.u10725 = KTree.node D2M8K2.t10734 (nat_lit 23284044) (nat_lit 2944299798) (nat_lit 0) D2M8K2.t10735 from rfl, totK_node, tot10734, tot10735]
  decide +kernel

theorem arows10729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10729 = true := by
  rw [show D2M8K2.u10729 = KTree.node D2M8K2.t10736 (nat_lit 23286323) (nat_lit 2907377834) (nat_lit 0) D2M8K2.t10737 from rfl, allE_node, rows10736, irow10729, rows10737]
  all_goals rfl

theorem atot10729 : totK PD2M8K2 D2M8K2.u10729 = [0, 0, 171679621030, 694519969792, 733094482999, 171453062004, 4934554315, 0] := by
  rw [show D2M8K2.u10729 = KTree.node D2M8K2.t10736 (nat_lit 23286323) (nat_lit 2907377834) (nat_lit 0) D2M8K2.t10737 from rfl, totK_node, tot10736, tot10737]
  decide +kernel

theorem arows10730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10730 = true := by
  rw [show D2M8K2.u10730 = KTree.node D2M8K2.t10738 (nat_lit 23308754) (nat_lit 1619926301) (nat_lit 8) D2M8K2.t10739 from rfl, allE_node, rows10738, irow10730, rows10739]
  all_goals rfl

theorem atot10730 : totK PD2M8K2 D2M8K2.u10730 = [0, 0, 236649340583, 778564649185, 628343970782, 91111401581, 1326647619, 0] := by
  rw [show D2M8K2.u10730 = KTree.node D2M8K2.t10738 (nat_lit 23308754) (nat_lit 1619926301) (nat_lit 8) D2M8K2.t10739 from rfl, totK_node, tot10738, tot10739]
  decide +kernel

theorem arows10732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10732 = true := by
  rw [show D2M8K2.u10732 = KTree.node D2M8K2.t10740 (nat_lit 23311192) (nat_lit 3674325927) (nat_lit 0) D2M8K2.t10741 from rfl, allE_node, rows10740, irow10732, rows10741]
  all_goals rfl

theorem atot10732 : totK PD2M8K2 D2M8K2.u10732 = [0, 0, 261539596591, 817946725177, 662215706837, 64907624295, 0, 0] := by
  rw [show D2M8K2.u10732 = KTree.node D2M8K2.t10740 (nat_lit 23311192) (nat_lit 3674325927) (nat_lit 0) D2M8K2.t10741 from rfl, totK_node, tot10740, tot10741]
  decide +kernel

theorem arows10733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10733 = true := by
  rw [show D2M8K2.u10733 = KTree.node D2M8K2.t10742 (nat_lit 23312800) (nat_lit 3746813931) (nat_lit 0) D2M8K2.t10743 from rfl, allE_node, rows10742, irow10733, rows10743]
  all_goals rfl

theorem atot10733 : totK PD2M8K2 D2M8K2.u10733 = [0, 0, 156503919853, 689736149580, 758320249393, 202674714982, 12570117775, 0] := by
  rw [show D2M8K2.u10733 = KTree.node D2M8K2.t10742 (nat_lit 23312800) (nat_lit 3746813931) (nat_lit 0) D2M8K2.t10743 from rfl, totK_node, tot10742, tot10743]
  decide +kernel

theorem arows10736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10736 = true := by
  rw [show D2M8K2.u10736 = KTree.node D2M8K2.t10744 (nat_lit 23314420) (nat_lit 3708134661) (nat_lit 0) D2M8K2.t10745 from rfl, allE_node, rows10744, irow10736, rows10745]
  all_goals rfl

theorem atot10736 : totK PD2M8K2 D2M8K2.u10736 = [0, 0, 256813777434, 793691805098, 619928477371, 127153143121, 2554132940, 0] := by
  rw [show D2M8K2.u10736 = KTree.node D2M8K2.t10744 (nat_lit 23314420) (nat_lit 3708134661) (nat_lit 0) D2M8K2.t10745 from rfl, totK_node, tot10744, tot10745]
  decide +kernel

theorem arows10737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10737 = true := by
  rw [show D2M8K2.u10737 = KTree.node D2M8K2.t10746 (nat_lit 23316055) (nat_lit 1206098616) (nat_lit 0) D2M8K2.t10747 from rfl, allE_node, rows10746, irow10737, rows10747]
  all_goals rfl

theorem atot10737 : totK PD2M8K2 D2M8K2.u10737 = [0, 0, 138955888048, 681334045673, 792070783875, 136227650119, 2109827372, 0] := by
  rw [show D2M8K2.u10737 = KTree.node D2M8K2.t10746 (nat_lit 23316055) (nat_lit 1206098616) (nat_lit 0) D2M8K2.t10747 from rfl, totK_node, tot10746, tot10747]
  decide +kernel

theorem arows10739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10739 = true := by
  rw [show D2M8K2.u10739 = KTree.node D2M8K2.t10748 (nat_lit 23318143) (nat_lit 2420449048) (nat_lit 0) D2M8K2.t10749 from rfl, allE_node, rows10748, irow10739, rows10749]
  all_goals rfl

theorem atot10739 : totK PD2M8K2 D2M8K2.u10739 = [0, 0, 350175261777, 899301213799, 486790885792, 51462025667, 2481160468, 0] := by
  rw [show D2M8K2.u10739 = KTree.node D2M8K2.t10748 (nat_lit 23318143) (nat_lit 2420449048) (nat_lit 0) D2M8K2.t10749 from rfl, totK_node, tot10748, tot10749]
  decide +kernel

theorem arows10740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10740 = true := by
  rw [show D2M8K2.u10740 = KTree.node D2M8K2.t10750 (nat_lit 23319723) (nat_lit 3703598000) (nat_lit 0) D2M8K2.t10751 from rfl, allE_node, rows10750, irow10740, rows10751]
  all_goals rfl

theorem atot10740 : totK PD2M8K2 D2M8K2.u10740 = [0, 0, 67023594919, 557648910070, 880974603455, 233732424840, 10540382461, 0] := by
  rw [show D2M8K2.u10740 = KTree.node D2M8K2.t10750 (nat_lit 23319723) (nat_lit 3703598000) (nat_lit 0) D2M8K2.t10751 from rfl, totK_node, tot10750, tot10751]
  decide +kernel

theorem arows10749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10749 = true := by
  rw [show D2M8K2.u10749 = KTree.node D2M8K2.t10752 (nat_lit 23321552) (nat_lit 3729112393) (nat_lit 0) D2M8K2.t10753 from rfl, allE_node, rows10752, irow10749, rows10753]
  all_goals rfl

theorem atot10749 : totK PD2M8K2 D2M8K2.u10749 = [0, 0, 349015103953, 878786525068, 513883941336, 68992807363, 2569691499, 0] := by
  rw [show D2M8K2.u10749 = KTree.node D2M8K2.t10752 (nat_lit 23321552) (nat_lit 3729112393) (nat_lit 0) D2M8K2.t10753 from rfl, totK_node, tot10752, tot10753]
  decide +kernel

theorem arows10750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10750 = true := by
  rw [show D2M8K2.u10750 = KTree.node D2M8K2.t10754 (nat_lit 23323016) (nat_lit 3564584354) (nat_lit 0) D2M8K2.t10755 from rfl, allE_node, rows10754, irow10750, rows10755]
  all_goals rfl

theorem atot10750 : totK PD2M8K2 D2M8K2.u10750 = [0, 0, 92932490688, 714768539178, 869665929842, 131738063281, 1096505104, 0] := by
  rw [show D2M8K2.u10750 = KTree.node D2M8K2.t10754 (nat_lit 23323016) (nat_lit 3564584354) (nat_lit 0) D2M8K2.t10755 from rfl, totK_node, tot10754, tot10755]
  decide +kernel

theorem arows10752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10752 = true := by
  rw [show D2M8K2.u10752 = KTree.node D2M8K2.t10756 (nat_lit 23328714) (nat_lit 1745988814) (nat_lit 0) D2M8K2.t10757 from rfl, allE_node, rows10756, irow10752, rows10757]
  all_goals rfl

theorem atot10752 : totK PD2M8K2 D2M8K2.u10752 = [0, 0, 0, 377231063815, 966038951920, 365871446628, 15869173497, 0] := by
  rw [show D2M8K2.u10752 = KTree.node D2M8K2.t10756 (nat_lit 23328714) (nat_lit 1745988814) (nat_lit 0) D2M8K2.t10757 from rfl, totK_node, tot10756, tot10757]
  decide +kernel

theorem arows10753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10753 = true := by
  rw [show D2M8K2.u10753 = KTree.node D2M8K2.t10758 (nat_lit 23330600) (nat_lit 3576313689) (nat_lit 0) D2M8K2.t10759 from rfl, allE_node, rows10758, irow10753, rows10759]
  all_goals rfl

theorem atot10753 : totK PD2M8K2 D2M8K2.u10753 = [0, 0, 0, 153488550701, 776276370056, 664954753788, 85271757005, 1138244013] := by
  rw [show D2M8K2.u10753 = KTree.node D2M8K2.t10758 (nat_lit 23330600) (nat_lit 3576313689) (nat_lit 0) D2M8K2.t10759 from rfl, totK_node, tot10758, tot10759]
  decide +kernel

theorem arows10756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10756 = true := by
  rw [show D2M8K2.u10756 = KTree.node D2M8K2.t10760 (nat_lit 23332787) (nat_lit 1301496664) (nat_lit 32) D2M8K2.t10761 from rfl, allE_node, rows10760, irow10756, rows10761]
  all_goals rfl

theorem atot10756 : totK PD2M8K2 D2M8K2.u10756 = [0, 0, 0, 537409582601, 956182665518, 283052481109, 8503517659, 0] := by
  rw [show D2M8K2.u10756 = KTree.node D2M8K2.t10760 (nat_lit 23332787) (nat_lit 1301496664) (nat_lit 32) D2M8K2.t10761 from rfl, totK_node, tot10760, tot10761]
  decide +kernel

theorem arows10757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10757 = true := by
  rw [show D2M8K2.u10757 = KTree.node D2M8K2.t10762 (nat_lit 23338450) (nat_lit 3791280686) (nat_lit 0) D2M8K2.t10763 from rfl, allE_node, rows10762, irow10757, rows10763]
  all_goals rfl

theorem atot10757 : totK PD2M8K2 D2M8K2.u10757 = [0, 0, 0, 428525363019, 956484666546, 344835319453, 18343323807, 0] := by
  rw [show D2M8K2.u10757 = KTree.node D2M8K2.t10762 (nat_lit 23338450) (nat_lit 3791280686) (nat_lit 0) D2M8K2.t10763 from rfl, totK_node, tot10762, tot10763]
  decide +kernel

theorem arows10759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10759 = true := by
  rw [show D2M8K2.u10759 = KTree.node D2M8K2.t10764 (nat_lit 23341886) (nat_lit 2916345944) (nat_lit 0) D2M8K2.t10765 from rfl, allE_node, rows10764, irow10759, rows10765]
  all_goals rfl

theorem atot10759 : totK PD2M8K2 D2M8K2.u10759 = [0, 0, 0, 399199859969, 947169771087, 400514523328, 23437804495, 0] := by
  rw [show D2M8K2.u10759 = KTree.node D2M8K2.t10764 (nat_lit 23341886) (nat_lit 2916345944) (nat_lit 0) D2M8K2.t10765 from rfl, totK_node, tot10764, tot10765]
  decide +kernel

theorem arows10760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10760 = true := by
  rw [show D2M8K2.u10760 = KTree.node D2M8K2.t10766 (nat_lit 23343124) (nat_lit 3522981391) (nat_lit 0) D2M8K2.t10767 from rfl, allE_node, rows10766, irow10760, rows10767]
  all_goals rfl

theorem atot10760 : totK PD2M8K2 D2M8K2.u10760 = [0, 0, 0, 190286219539, 814395858228, 633884764147, 80999151431, 1095107716] := by
  rw [show D2M8K2.u10760 = KTree.node D2M8K2.t10766 (nat_lit 23343124) (nat_lit 3522981391) (nat_lit 0) D2M8K2.t10767 from rfl, totK_node, tot10766, tot10767]
  decide +kernel

theorem arows10764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10764 = true := by
  rw [show D2M8K2.u10764 = KTree.node D2M8K2.t10768 (nat_lit 23390402) (nat_lit 3122939410) (nat_lit 0) D2M8K2.t10769 from rfl, allE_node, rows10768, irow10764, rows10769]
  all_goals rfl

theorem atot10764 : totK PD2M8K2 D2M8K2.u10764 = [0, 263896442175, 637260384088, 283246052116, 177815729807, 318744042507, 93467172928, 3882006667] := by
  rw [show D2M8K2.u10764 = KTree.node D2M8K2.t10768 (nat_lit 23390402) (nat_lit 3122939410) (nat_lit 0) D2M8K2.t10769 from rfl, totK_node, tot10768, tot10769]
  decide +kernel

theorem arows10765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10765 = true := by
  rw [show D2M8K2.u10765 = KTree.node D2M8K2.t10770 (nat_lit 23391923) (nat_lit 2976637533) (nat_lit 0) D2M8K2.t10771 from rfl, allE_node, rows10770, irow10765, rows10771]
  all_goals rfl

theorem atot10765 : totK PD2M8K2 D2M8K2.u10765 = [0, 169597878671, 734926473250, 756259486626, 127567899769, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10765 = KTree.node D2M8K2.t10770 (nat_lit 23391923) (nat_lit 2976637533) (nat_lit 0) D2M8K2.t10771 from rfl, totK_node, tot10770, tot10771]
  decide +kernel

theorem arows10767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10767 = true := by
  rw [show D2M8K2.u10767 = KTree.node D2M8K2.t10772 (nat_lit 23397464) (nat_lit 3096845491) (nat_lit 0) D2M8K2.t10773 from rfl, allE_node, rows10772, irow10767, rows10773]
  all_goals rfl

theorem atot10767 : totK PD2M8K2 D2M8K2.u10767 = [0, 294123808781, 855230311298, 589315627441, 61115479150, 0, 0, 0] := by
  rw [show D2M8K2.u10767 = KTree.node D2M8K2.t10772 (nat_lit 23397464) (nat_lit 3096845491) (nat_lit 0) D2M8K2.t10773 from rfl, totK_node, tot10772, tot10773]
  decide +kernel

theorem arows10768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10768 = true := by
  rw [show D2M8K2.u10768 = KTree.node D2M8K2.t10774 (nat_lit 23399113) (nat_lit 1432750075) (nat_lit 0) D2M8K2.t10775 from rfl, allE_node, rows10774, irow10768, rows10775]
  all_goals rfl

theorem atot10768 : totK PD2M8K2 D2M8K2.u10768 = [0, 87208453540, 614507587596, 871907632742, 204889378938, 5398830306, 0, 0] := by
  rw [show D2M8K2.u10768 = KTree.node D2M8K2.t10774 (nat_lit 23399113) (nat_lit 1432750075) (nat_lit 0) D2M8K2.t10775 from rfl, totK_node, tot10774, tot10775]
  decide +kernel

theorem arows10771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10771 = true := by
  rw [show D2M8K2.u10771 = KTree.node D2M8K2.t10776 (nat_lit 23401453) (nat_lit 1384173910) (nat_lit 0) D2M8K2.t10777 from rfl, allE_node, rows10776, irow10771, rows10777]
  all_goals rfl

theorem atot10771 : totK PD2M8K2 D2M8K2.u10771 = [0, 361898951789, 920019389093, 492321187399, 42789043682, 0, 0, 0] := by
  rw [show D2M8K2.u10771 = KTree.node D2M8K2.t10776 (nat_lit 23401453) (nat_lit 1384173910) (nat_lit 0) D2M8K2.t10777 from rfl, totK_node, tot10776, tot10777]
  decide +kernel

theorem arows10772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10772 = true := by
  rw [show D2M8K2.u10772 = KTree.node D2M8K2.t10778 (nat_lit 23402724) (nat_lit 2659905950) (nat_lit 0) D2M8K2.t10779 from rfl, allE_node, rows10778, irow10772, rows10779]
  all_goals rfl

theorem atot10772 : totK PD2M8K2 D2M8K2.u10772 = [0, 49139168205, 523292903448, 902290601985, 288655645422, 13250685261, 0, 0] := by
  rw [show D2M8K2.u10772 = KTree.node D2M8K2.t10778 (nat_lit 23402724) (nat_lit 2659905950) (nat_lit 0) D2M8K2.t10779 from rfl, totK_node, tot10778, tot10779]
  decide +kernel

theorem arows10774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10774 = true := by
  rw [show D2M8K2.u10774 = KTree.node D2M8K2.t10780 (nat_lit 23404905) (nat_lit 1829442760) (nat_lit 0) D2M8K2.t10781 from rfl, allE_node, rows10780, irow10774, rows10781]
  all_goals rfl

theorem atot10774 : totK PD2M8K2 D2M8K2.u10774 = [0, 323573965860, 913751506176, 505781431096, 45609432998, 0, 0, 0] := by
  rw [show D2M8K2.u10774 = KTree.node D2M8K2.t10780 (nat_lit 23404905) (nat_lit 1829442760) (nat_lit 0) D2M8K2.t10781 from rfl, totK_node, tot10780, tot10781]
  decide +kernel

theorem arows10775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10775 = true := by
  rw [show D2M8K2.u10775 = KTree.node D2M8K2.t10782 (nat_lit 23407024) (nat_lit 3392280839) (nat_lit 0) D2M8K2.t10783 from rfl, allE_node, rows10782, irow10775, rows10783]
  all_goals rfl

theorem atot10775 : totK PD2M8K2 D2M8K2.u10775 = [0, 161042149573, 679437759760, 767609193777, 175274590169, 4980514959, 0, 0] := by
  rw [show D2M8K2.u10775 = KTree.node D2M8K2.t10782 (nat_lit 23407024) (nat_lit 3392280839) (nat_lit 0) D2M8K2.t10783 from rfl, totK_node, tot10782, tot10783]
  decide +kernel

theorem arows10780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10780 = true := by
  rw [show D2M8K2.u10780 = KTree.node D2M8K2.t10784 (nat_lit 23408610) (nat_lit 3310672824) (nat_lit 0) D2M8K2.t10785 from rfl, allE_node, rows10784, irow10780, rows10785]
  all_goals rfl

theorem atot10780 : totK PD2M8K2 D2M8K2.u10780 = [0, 264732260305, 789296353714, 641591633752, 105077253939, 1268739303, 0, 0] := by
  rw [show D2M8K2.u10780 = KTree.node D2M8K2.t10784 (nat_lit 23408610) (nat_lit 3310672824) (nat_lit 0) D2M8K2.t10785 from rfl, totK_node, tot10784, tot10785]
  decide +kernel

theorem arows10781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10781 = true := by
  rw [show D2M8K2.u10781 = KTree.node D2M8K2.t10786 (nat_lit 23410252) (nat_lit 2459017574) (nat_lit 0) D2M8K2.t10787 from rfl, allE_node, rows10786, irow10781, rows10787]
  all_goals rfl

theorem atot10781 : totK PD2M8K2 D2M8K2.u10781 = [0, 0, 419448406888, 949859094360, 384602474774, 22149860293, 0, 0] := by
  rw [show D2M8K2.u10781 = KTree.node D2M8K2.t10786 (nat_lit 23410252) (nat_lit 2459017574) (nat_lit 0) D2M8K2.t10787 from rfl, totK_node, tot10786, tot10787]
  decide +kernel

theorem arows10783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10783 = true := by
  rw [show D2M8K2.u10783 = KTree.node D2M8K2.t10788 (nat_lit 23412069) (nat_lit 1450045145) (nat_lit 0) D2M8K2.t10789 from rfl, allE_node, rows10788, irow10783, rows10789]
  all_goals rfl

theorem atot10783 : totK PD2M8K2 D2M8K2.u10783 = [0, 0, 340152237197, 925075152667, 445528329557, 29630079498, 0, 0] := by
  rw [show D2M8K2.u10783 = KTree.node D2M8K2.t10788 (nat_lit 23412069) (nat_lit 1450045145) (nat_lit 0) D2M8K2.t10789 from rfl, totK_node, tot10788, tot10789]
  decide +kernel

theorem arows10784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10784 = true := by
  rw [show D2M8K2.u10784 = KTree.node D2M8K2.t10790 (nat_lit 23413892) (nat_lit 2785564950) (nat_lit 8) D2M8K2.t10791 from rfl, allE_node, rows10790, irow10784, rows10791]
  all_goals rfl

theorem atot10784 : totK PD2M8K2 D2M8K2.u10784 = [0, 0, 140854072676, 730978996216, 744451598563, 120736073050, 1369150432, 0] := by
  rw [show D2M8K2.u10784 = KTree.node D2M8K2.t10790 (nat_lit 23413892) (nat_lit 2785564950) (nat_lit 8) D2M8K2.t10791 from rfl, totK_node, tot10790, tot10791]
  decide +kernel

theorem arows10787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10787 = true := by
  rw [show D2M8K2.u10787 = KTree.node D2M8K2.t10792 (nat_lit 23419352) (nat_lit 3028461896) (nat_lit 0) D2M8K2.t10793 from rfl, allE_node, rows10792, irow10787, rows10793]
  all_goals rfl

theorem atot10787 : totK PD2M8K2 D2M8K2.u10787 = [0, 0, 396501456129, 965515843597, 407996222952, 17000976467, 0, 0] := by
  rw [show D2M8K2.u10787 = KTree.node D2M8K2.t10792 (nat_lit 23419352) (nat_lit 3028461896) (nat_lit 0) D2M8K2.t10793 from rfl, totK_node, tot10792, tot10793]
  decide +kernel

theorem arows10788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10788 = true := by
  rw [show D2M8K2.u10788 = KTree.node D2M8K2.t10794 (nat_lit 23422665) (nat_lit 1795282089) (nat_lit 0) D2M8K2.t10795 from rfl, allE_node, rows10794, irow10788, rows10795]
  all_goals rfl

theorem atot10788 : totK PD2M8K2 D2M8K2.u10788 = [0, 0, 343145252894, 939865695595, 473728751591, 26624665612, 0, 0] := by
  rw [show D2M8K2.u10788 = KTree.node D2M8K2.t10794 (nat_lit 23422665) (nat_lit 1795282089) (nat_lit 0) D2M8K2.t10795 from rfl, totK_node, tot10794, tot10795]
  decide +kernel

theorem arows10790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10790 = true := by
  rw [show D2M8K2.u10790 = KTree.node D2M8K2.t10796 (nat_lit 23426006) (nat_lit 3628826306) (nat_lit 0) D2M8K2.t10797 from rfl, allE_node, rows10796, irow10790, rows10797]
  all_goals rfl

theorem atot10790 : totK PD2M8K2 D2M8K2.u10790 = [0, 0, 397148021836, 969871697872, 398683914113, 14921544271, 0, 0] := by
  rw [show D2M8K2.u10790 = KTree.node D2M8K2.t10796 (nat_lit 23426006) (nat_lit 3628826306) (nat_lit 0) D2M8K2.t10797 from rfl, totK_node, tot10796, tot10797]
  decide +kernel

theorem arows10791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10791 = true := by
  rw [show D2M8K2.u10791 = KTree.node D2M8K2.t10798 (nat_lit 23429337) (nat_lit 1694538032) (nat_lit 0) D2M8K2.t10799 from rfl, allE_node, rows10798, irow10791, rows10799]
  all_goals rfl

theorem atot10791 : totK PD2M8K2 D2M8K2.u10791 = [0, 94311201580, 471438678916, 812420794290, 406780476642, 27046029162, 0, 0] := by
  rw [show D2M8K2.u10791 = KTree.node D2M8K2.t10798 (nat_lit 23429337) (nat_lit 1694538032) (nat_lit 0) D2M8K2.t10799 from rfl, totK_node, tot10798, tot10799]
  decide +kernel

end QECKChecks.D2M8K2
